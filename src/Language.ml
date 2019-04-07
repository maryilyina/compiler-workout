(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

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
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)

    let to_integer bin_val = 
      if bin_val then 1 else 0

    let to_bool int_val =
      if int_val != 0 then true else false

    let eval_binop op x y =
      match op with
        | "+" -> x + y
        | "-" -> x - y
        | "*" -> x * y
        | "/" -> x / y
        | "%" -> x mod y
        | ">"  -> to_integer(x > y)
        | "<"  -> to_integer(x < y)
        | ">=" -> to_integer(x >= y)
        | "<=" -> to_integer(x <= y)
        | "==" -> to_integer(x = y)
        | "!=" -> to_integer(x <> y)
        | "&&" -> to_integer((to_bool x) && (to_bool y))
        | "!!" -> to_integer((to_bool x) || (to_bool y))
        | _    -> failwith "Not implemented"

    let rec eval st expr =
      match expr with 
        | Const c  -> c
        | Var v    -> st v
        | Binop(op, x, y) -> eval_binop op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    let ($) f x = f x

    let binop_parser xs = 
      List.map (
        fun x -> ostap (- $(x)), 
        (fun l r -> Binop (x, l, r))
      ) xs;;

    ostap (
      expr: 
        !(Ostap.Util.expr
          (fun x -> x)
          [|
            `Lefta, binop_parser ["!!"];
            `Lefta, binop_parser ["&&"];
            `Nona,  binop_parser ["<="; ">="; "<"; ">"; "=="; "!="];
            `Lefta, binop_parser ["+"; "-"];
            `Lefta, binop_parser ["*"; "/"; "%"];
          |]
          primary
        );
      primary: 
          x:IDENT   { Var x } 
        | n:DECIMAL { Const n } 
        | -"(" expr -")"
    )
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read         of string
    (* write the value of an expression *) | Write        of Expr.t
    (* assignment                       *) | Assign       of string * Expr.t
    (* composition                      *) | Seq          of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If           of Expr.t * t * t
    (* loop with a pre-condition        *) | While        of Expr.t * t
    (* loop with a post-condition       *) | RepeatUntil  of t * Expr.t  with show
    (* call a procedure                 *) | Call         of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval (s, i, o) statement =
      match statement with
        | Read x -> 
            (let head::tail = i in
            Expr.update x head s, tail, o)
        | Write e       -> (s, i, o@[Expr.eval s e])
        | Assign (x, e) -> (Expr.update x (Expr.eval s e) s, i, o) 
        | Seq    (a, b) -> eval (eval (s, i, o) a) b  
        | If (what, first, second)  -> 
              eval (s, i, o) 
              (if Expr.eval s what == 0 then second else first)
        | While (what, body)  ->
            (if Expr.eval s what == 0 then (s, i, o)
            else 
              let repeatition = While (what, body) in 
              eval (eval (s, i, o) body) repeatition)
        | RepeatUntil (body, what) ->
            let repeatition = While (Expr.Binop ("==", what, Expr.Const 0), body) in
              eval (eval (s, i, o) body) repeatition
        | Skip -> (s, i, o)
        
    (* Statement parser *)
    ostap (
      statement: 
          "read"    "("   x:IDENT        ")"  { Read   x    }
        | "write"   "("   e:!(Expr.expr) ")"  { Write  e    }
        | x:IDENT   ":="  e:!(Expr.expr)      { Assign(x, e)}
        
        | "if" what:!(Expr.expr) "then" first:!(parse)
          elif_branch: (%"elif" !(Expr.expr) %"then" !(parse))*
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
        | "while" what:!(Expr.expr) "do" body:!(parse) "od" { While (what, body) }
        | "repeat" body:!(parse) "until" what:!(Expr.expr) { RepeatUntil (body, what) }
        | "for" what:!(parse) "," cond:!(Expr.expr) "," step:!(parse) "do" body:!(parse)
          "od" { Seq (what, While (cond, Seq (body, step))) }
        | "skip" { Skip };
      parse: line:statement ";" tail:parse { Seq (line, tail) } | statement
    ) 
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (                                      
      parse: empty {failwith "Not yet implemented"}
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
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
