(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open List
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

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
            `Nona,  binop_parser ["<"; ">"; "<="; ">="; "=="; "!="];
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
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (s, i, o) statement = 
      match statement with
        | Read x -> 
            (let head::tail = i in
            Expr.update x head s, tail, o)
        | Write e       -> (s, i, o@[Expr.eval s e])
        | Assign (x, e) -> (Expr.update x (Expr.eval s e) s, i, o) 
        | Seq    (a, b) -> eval (eval (s, i, o) a) b           

    (* Statement parser *)
    ostap (
      statement: 
          "read"    "("   x:IDENT        ")"  { Read   x    }
        | "write"   "("   e:!(Expr.expr) ")"  { Write  e    }
        | x:IDENT   ":="  e:!(Expr.expr)      { Assign(x, e)};

      parse: line:statement ";" tail:parse { Seq (line, tail) } | statement
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
