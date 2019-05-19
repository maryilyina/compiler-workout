(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of bytes | Array of t array | Sexp of string * t list (*with show*)

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = Bytes.set s i x; s 
    let update_array  a i x = a.(i) <- x; a
                      
  end
  
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code (Bytes.get s i)
                                     | Value.Array    a  -> a.(i)
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"     -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Sexp (_, a) -> List.length a | Value.Array a -> Array.length a | Value.String s -> Bytes.length s)))
    | ".array"      -> (st, i, o, Some (Value.of_array @@ Array.of_list args))
    | ".string"     ->
       let make_string str = Some (Value.String (Bytes.of_string str)) in
       let rec convert value = 
         match value with
         | (Value.String bytes as str) ->
            Printf.sprintf "\"%s\"" (Bytes.to_string bytes)
         | (Value.Int num) -> string_of_int num
         | (Value.Array elements) ->
            let elements = String.concat ", " (List.map convert (Array.to_list elements)) in
            Printf.sprintf "[%s]" elements
         | (Value.Sexp (name, elements)) ->
            if (List.length elements != 0)
            then let elements = String.concat ", " (List.map convert elements) in
                 Printf.sprintf "`%s (%s)" name elements
            else Printf.sprintf "`%s" name
       in (st, i, o, make_string (convert (List.hd args)))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))   
    | x -> failwith (Printf.sprintf "Unknown fun: %s" x)
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator
          val eval : env -> config -> t -> int * config
       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method
           method definition : env -> string -> int list -> config -> config
       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
 

let rec eval env ((st, i, o, r) as conf) expr =
     match expr with
      | Const n             -> (st, i, o, Some Value.of_int n)
      | Var x               -> (st, i, o, Some (State.eval st x))
      | Binop (op, x, y)    -> let ((_, _, _, Some a) as conf') = eval env conf x in
                              let (st', i', o', Some b)        = eval env conf' y in
                              (st', i', o', Some (Value.of_int @@ to_func op (Value.to_int a) (Value.to_int b)))
      | Array elems         -> let (st, i, o, v) = eval_list env conf elems in
                              env#definition env ".array" v (st, i, o, None)
      | Elem (a, idx)       -> let (st, i, o, v)  = eval_list env conf [a; idx] in
                              env#definition env ".elem" v (st, i, o, None)
      | Length a            -> let (st, i, o, v) = eval_list env conf [a] in
                              env#definition env ".length" v (st, i, o, None)
      | String s            -> (st, i, o, Some Value.of_string (Bytes.of_string s))
      | Sexp (n, s)         -> let (st, i, o, v) = eval_list env conf s in
                              (st, i, o, Some Value.Sexp (n, v))
      | Call (name, params) -> let (st, i, o, params) = eval_list env conf params in
		                          env#definition env name params (st, i, o, None)

    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    let rec build_index_sequence expr indices = 
      match indices with
        | [] -> expr
        | index::rest -> build_index_sequence (Elem (expr, index)) rest

    ostap (                                      
      parse:
    	    !(Ostap.Util.expr
                (fun x -> x)
    	        (Array.map (fun (a, s) -> a,
                               List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                            )
                  [|
    		        `Lefta, ["!!"];
    		        `Lefta, ["&&"];
    		        `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
    		        `Lefta, ["+" ; "-"];
    		        `Lefta, ["*" ; "/"; "%"];
                  |]
    	    )
    	    str_part);

      str_part:
        idx:primary str_opt:".string"? {
            match str_opt with 
            | Some _ -> Call (".string", [idx]) 
            | None -> idx
          };

      primary: 
          e: base elems: (-"[" !(parse) -"]")* len: (".length")? {
              let with_elems = List.fold_left (fun e ind -> Elem (e, ind)) e elems in
              match len with
                  | Some _ -> Length with_elems
                  | _ -> with_elems
            };
          
      base:
          n:DECIMAL                                 
          {Const n}
          | s:STRING                                {String (String.sub s 1 (String.length s - 2))}
          | c:CHAR                                  {Const (Char.code c)}
          | "[" elems:!(Util.list0 parse) "]"       {Array elems}
          | x:IDENT call:( -"(" params:lst? -")" )? {
              let unwrap o = match o with
                | None -> []
                | Some results -> results in 
              match call with 
                Some args -> Call (x, unwrap args) 
                | None -> Var x
            }
          | -"(" parse -")"
          | "`" name:IDENT subs:((-"(" (!(Util.list)[parse]) -")")?) {
                match subs with
                  Some s -> Sexp(name, s)
                  | None -> Sexp(name, [])
              };

      lst:
          a:parse "," tail:lst {a::tail} |
          a:parse              {[a]}
    )
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse: 
            "_"              {Wildcard}
            | name:IDENT     {Ident name}
            | "`" name:IDENT subs_opt:((-"(" (!(Util.list)[parse]) -")")?) {
              match subs_opt with 
                  Some subs -> Sexp (name, subs) 
                  | None -> Sexp (name, [])
            }
        )
        let vars p =
         transform(t) (fun f -> object inherit [string list, _] @t[foldl] f method c_Ident s _ name = name::s end) [] p  
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator
         val eval : env -> config -> t -> config
       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in (
            match a with
              | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
              | Value.Array a               -> Value.Array  (Value.update_array  a i (update a.(i) v tl))
      ) in
      State.update x (
          match is with 
          [] -> v 
          | _ -> update (State.eval st x) v is) 
      st

    let is_some = function
      | Some _ -> true
      | None -> false

    let rec match_pattern value pattern = match pattern with
      | Pattern.Wildcard -> Some []
      | Pattern.Ident var -> Some [(var, value)]
      | Pattern.Sexp (name, subpatterns) ->
          match value with
            | Value.Sexp (name', subvalues) ->
                if (name = name') && (List.length subpatterns = List.length subvalues)
                then
                  let subresults = List.map2 match_pattern subvalues subpatterns in
                  if List.for_all (is_some) subresults
                  then
                    Some (List.concat (List.map (fun (Some lst) -> lst) subresults))
                  else None
                else None
            | _ -> failwith "Tried to match pattern with non-sexp"
                  
    let perform_or_skip s2 s1 =
      match s2 with
      | Skip -> s1
      | _ -> Seq (s1, s2)

    let rec eval env ((s, i, o, r) as conf) k statement =
        let evaluate_expr expr = Expr.eval env conf expr in
        match statement with
          | Assign (x, ids, e) -> 
              let (s, i, o, ids) = Expr.eval_list env conf ids in
              let (s, i, o, Some r) = evaluate_expr e in
              eval env (update s x r ids, i, o, None) Skip k
          | Seq (a, b) -> eval env conf (perform_or_skip k b) a
          | Skip -> (
              match k with
              | Skip -> conf
              | _ -> eval env conf Skip k
          )
          | Seq (a, b) -> eval env conf (perform_or_skip k b) a
          | If (what, body1, body2) -> 
              let ((s, i, o, Some r) as conf') = evaluate_expr what in
              if Value.to_int r != 0 
                then eval env conf' k body1
                else eval env conf' k body2
          | While (what, body) ->
              let (s, i, o, Some n) = evaluate_expr what in
              if Value.to_int n = 0 
                then eval env (s, i, o, r) Skip k
                else eval env (s, i, o, r) (perform_or_skip k statement) body
          | Repeat (body, what) ->
              let repeatition = Expr.Binop ("==", what, Expr.Const 0) in 
              eval env conf (perform_or_skip k (While (repeatition, body))) body
          | Call (name, params) -> 
              eval env (evaluate_expr (Expr.Call (name, params))) Skip k
          | Return x -> (match x with
                | Some x -> evaluate_expr x
                | None   -> conf)
          | Case (what, branches) ->
            let (s, i, o, Some value) = evaluate_expr what in
            let try_to_match (pattern, stmt) =
              match (match_pattern value pattern) with
                | Some lst -> Some (lst, stmt)
                | None -> None in
            let (Some (branch_locals, stmt)) = List.find (is_some) (List.map try_to_match branches) in
            let (branch_vars, _) = List.split branch_locals in
            let branch_state = List.fold_left (fun s (var, value) -> State.update var value s) 
                (State.push s State.undefined branch_vars) branch_locals in
            let (s, i, o, res) = eval env (branch_state, i, o, None) Skip stmt in
            let s = State.drop s in
            eval env (s, i, o, res) Skip k
            
    (* Statement parser *)
    ostap (
      pattern_match: 
        p:!(Pattern.parse) "->" result:parse {(p, result)};

      statement: 
        x:IDENT ids: (-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse)
                {Assign (x, ids, e)}
        | "if" what:!(Expr.parse) "then" first:!(parse)
          elif_branch: (%"elif" !(Expr.parse) %"then" !(parse))*
          els_branch:  (%"else" !(parse))?
          "fi" { 
              let els_body = match els_branch with
                | Some x -> x
                | _ -> Skip
              in 
              let expanded = List.fold_right 
                  (fun (cond, body) else_body -> 
                    If (cond, body, else_body)) elif_branch els_body 
              in If (what, first, expanded) 
            }
            
        | "while" what:!(Expr.parse) "do" body:!(parse) "od"          
                  { While (what, body) }
        | "repeat" body:!(parse) "until" what:!(Expr.parse)
                  { Repeat (body, what) }
        | "for" what:!(parse) "," cond:!(Expr.parse) "," step:!(parse) "do" body:!(parse)
          "od"    { Seq (what, While (cond, Seq (body, step))) }
        | "skip"  { Skip }

        | funct:IDENT "(" args:( !(Expr.parse) )* ")" 
                  { Call (funct, args) }
        | "return" e:!(Expr.parse)? 
                  { Return e }

        | "case" x:!(Expr.parse) "of" variants:(!(Util.listBy)[ostap ("|")][pattern_match]) 
          "esac" { Case (x,variants) };

      parse: 
        line:statement ";" tail:parse 
                { Seq (line, tail) } 
        | statement
    
    )
      
  end

(* Function and procedure definitions *)
  
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))? 
         "{" body:!(Stmt.parse) "}"
        { (name, (args, (match locs with None -> [] | Some l -> l), body)) }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator
     eval : t -> int list -> int list
   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))