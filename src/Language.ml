(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

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
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)                                                           let to_func op =
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
          | Const n                 -> (st, i, o, Some n)
          | Var x                   -> (st, i, o, Some (State.eval st x))
          | Binop (op, x, y)        -> let ((_, _, _, Some a) as conf') = eval env conf x in
                                       let (st', i', o', Some b)        = eval env conf' y in
                                       (st', i', o', Some (to_func op a b))
          | Call (name, params)     -> let (st', i', o', vals) =
                                           List.fold_left
                                           (
                                                fun (st, i, o, vals) e ->
                                                    let ((st, i, o, Some r) as conf) = eval env conf e in
                                                    (st, i, o, vals @ [r])
                                           ) (st, i, o, []) params in
                                        env#definition env name vals (st', i', o', None)


         
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
        n:DECIMAL {Const n}
        | -"(" parse -")"
        | name:IDENT p:("(" args:!(Ostap.Util.list0 parse) ")" {Call (name, args)} | empty {Var name}) {p}
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
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

    let meta_op s2 s1 =
      match s2 with
      | Skip -> s1
      | _ -> Seq (s1, s2)

    let rec eval env ((s, i, o, r) as conf) k statement = 
       match statement with
        | Read x -> 
            let head::tail = i in
            eval env (State.update x head s, tail, o, None) Skip k
        | Write e       -> 
            let (s, i, o, Some r) = Expr.eval env conf e in 
            eval env (s, i, o @ [r], None) Skip k

        | Assign (x, e)              
            -> let (s, i, o, Some r) = Expr.eval env conf e in
            eval env (State.update x r s, i, o, Some r) Skip k
        | Seq (a, b) -> eval env conf (meta_op k b) a
        | Skip -> (
            match k with
            | Skip -> conf
            | _ -> eval env conf Skip k
          )
        | Seq (a, b) -> eval env conf (meta_op k b) a
        | If (cond, body1, body2)        
            -> let ((s, i, o, Some r) as conf') = Expr.eval env conf cond in
            if r != 0 then eval env conf' k body1
            else eval env conf' k body2
        | While (what, body) ->
            let (s', i', o', Some n) = Expr.eval env conf what in
            if n = 0 then
                eval env (s', i', o', r) Skip k
            else
                eval env (s', i', o', r) (meta_op k statement) body

        | Repeat (body, what) ->
            eval env conf (meta_op k (While (Expr.Binop ("==", what, Expr.Const 0), body))) body
        
        | Call (name, params) -> 
            eval env (Expr.eval env conf (Expr.Call (name, params))) Skip k
        | Return x -> 
            (match x with
              | Some x -> Expr.eval env conf x
              | None   -> conf
            )

    (* Statement parser *)
    ostap (                                      
      call_statement:
        funct:IDENT "(" args:( !(Expr.parse) )* ")" { Call (funct, args) };

      statement: 
          "read"    "("   x:IDENT         ")"  { Read   x    }
        | "write"   "("   e:!(Expr.parse) ")"  { Write  e    }
        | x:IDENT   ":="  e:!(Expr.parse)      { Assign(x, e)}
        
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
      parse: "fun" f:IDENT "(" args:!(Util.list0 arg) ")" locals:(%"local" !(Util.list arg))? "{" body:!(Stmt.parse) "}"
      {
          let locals =
              match locals with
              | Some x -> x
              | _ -> []
          in
          f, (args, locals, body)
      }
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
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
