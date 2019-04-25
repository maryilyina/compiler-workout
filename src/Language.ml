(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let rec list_init iter n f =
  if iter < n
  then (f iter) :: (list_init (iter + 1) n f)
  else []

let unwrap o = match o with
        | None -> []
        | Some l -> l

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = list_init 0 (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )         
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
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

    let rec eval env ((st, i, o, r) as conf) expr = match expr with
        | Const n                 -> (st, i, o, Some Value.of_int n)
        | Var x                   -> (st, i, o, Some (State.eval st x))
        | Binop (op, x, y)        -> let ((_, _, _, Some a) as conf') = eval env conf x in
                                   let (st', i', o', Some b)        = eval env conf' y in
                                   (st', i', o', Some (Value.of_int @@ to_func op (Value.to_int a) (Value.to_int b)))
        | Call (name, params)     -> let (st', i', o', vals) =
                                       List.fold_left
                                       (
                                            fun (st, i, o, vals) e ->
                                                let ((st, i, o, Some r) as conf) = eval env conf e in
                                                (st, i, o, vals @ [r])
                                       ) (st, i, o, []) params in
                                    env#definition env name vals (st', i', o', None)
        | Array elems             -> let (st', i', o', elems) = eval_list env conf elems in
                                     (st', i', o', Some (Value.of_array elems))
        | String str              -> (st, i, o, Some (Value.of_string str))
        | Elem (a, index)         -> let ((_, _, _, Some index) as conf) = eval env conf index in
                                     let (st', i', o', Some a) = eval env conf a in
                                     let value = match a with
                                                  | String s -> Value.of_int @@ Char.code s.[Value.to_int index]
                                                  | Array ary -> List.nth ary (Value.to_int index) in
                                     (st', i', o', Some value)
        | Length x                -> let (st', i', o', Some x) = eval env conf x in
                                     (st', i', o', Some (match x with
                                                            | Value.String s -> Value.of_int @@ String.length s
                                                            | Value.Array a -> Value.of_int @@ List.length a))
    
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
         primary);

      primary:
          e: base elems: (-"[" !(parse) -"]")* len: (".length")?
              {
                  let with_elems = List.fold_left (fun e ind -> Elem (e, ind)) e elems in
                  match len with
                      | Some _ -> Length with_elems
                      | _ -> with_elems
              };
      base:
          n:DECIMAL                               {Const n} |
          s:STRING                                {String (String.sub s 1 (String.length s - 2))} |
          c:CHAR                                  {Const (Char.code c)} |
          "[" elems:!(Util.list0 parse) "]"       {Array elems} |
          x:IDENT call:( -"(" params:lst? -")" )? {match call with Some args -> Call (x, unwrap args) | None -> Var x} |
          -"(" parse -")";
      lst:
          a:parse "," tail:lst {a::tail} |
          a:parse              {[a]}
    )
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator
         val eval : env -> config -> t -> config
       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st
          
    let perform_or_skip s2 s1 =
      match s2 with
      | Skip -> s1
      | _ -> Seq (s1, s2)

    let evaluate_expr e c expr =
      Expr.eval e c expr
      
    let rec eval env ((s, i, o, r) as conf) k statement =
        match statement with
            | Assign (x, is, e) -> 
                let (s, i, o, is) = Expr.eval_list env conf is in
                let (s, i, o, Some r) = evaluate_expr env (s, i, o, None) e in
                eval env (update s x r is, i, o, None) Skip k
            | Seq (a, b) -> 
                eval env conf (perform_or_skip k b) a
            | Skip -> (
                match k with
                | Skip -> conf
                | _ -> eval env conf Skip k
            )
            | Seq (a, b) -> eval env conf (perform_or_skip k b) a
            | If (what, body1, body2) -> 
                let ((s, i, o, Some r) as conf') = evaluate_expr env conf what in
                if Value.to_int r != 0 then eval env conf' k body1
                else eval env conf' k body2
            | While (what, body) ->
                let (s', i', o', Some n) = evaluate_expr env conf what in
                if Value.to_int n = 0 then
                    eval env (s', i', o', r) Skip k
                else
                    eval env (s', i', o', r) (perform_or_skip k statement) body

            | Repeat (body, what) ->
              let repeatition = Expr.Binop ("==", what, Expr.Const 0) in 
              eval env conf (perform_or_skip k (While (repeatition, body))) body
            
            | Call (name, params) -> 
                eval env (evaluate_expr env conf (Expr.Call (name, params))) Skip k
            | Return x -> 
                match x with
                  | Some x -> evaluate_expr env conf x
                  | None   -> conf
            
    (* Statement parser *)
  ostap (                                      
      call_statement:
        funct:IDENT "(" args:( !(Expr.parse) )* ")" { Call (funct, args) };

      statement: 
        x:IDENT ids: (-"[" !(Expr.parse) -"]")* ":="
                e:!(Expr.parse) {Assign (x, ids, e)}
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
        | "while" what:!(Expr.parse) "do" body:!(parse) "od" { While (what, body) }
        | "repeat" body:!(parse) "until" what:!(Expr.parse) { Repeat (body, what) }
        | "for" what:!(parse) "," cond:!(Expr.parse) "," step:!(parse) "do" body:!(parse)
          "od" { Seq (what, While (cond, Seq (body, step))) }
        | "skip" { Skip }
        | call: call_statement { call }
        | "return" e:!(Expr.parse)? { Return e };

      parse: line:statement ";" tail:parse { Seq (line, tail) } | statement
    )
      
  end
(* Function and procedure definitions *)
let get_or_default def_val = function
  | Some x -> x
  | _      -> def_val

module Definition =
  struct
    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)
    ostap (                                      
      arg: IDENT;
      parse: 
        "fun" f:IDENT "(" args:!(Util.list0 arg) ")" 
        locals:(%"local" !(Util.list arg))? 
        "{" body:!(Stmt.parse) "}"
        { f, (args, get_or_default [] locals, body) }
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