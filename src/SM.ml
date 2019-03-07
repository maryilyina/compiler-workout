open GT  
open List     
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Language.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *) 
 
let execute_instr (stack, (s, i, o)) instr = match instr with 
  | BINOP op -> 
      let y :: x :: rest = stack in 
      ((Language.Expr.eval_binop op x y) :: rest, (s, i, o)) 
  | CONST c -> (c :: stack, (s, i, o))
  | READ -> 
      let z :: rest = i in
      (z :: stack, (s, rest, o))
  | WRITE -> 
      let z :: rest = stack in
      (rest, (s, i, o @ [z]))
  | LD x -> ((s x) :: stack, (s, i, o))
  | ST x -> 
      let z :: rest = stack in
      (rest, (Language.Expr.update x z s, i, o))

let rec eval conf prg = match prg with
  | instr :: rest -> eval (execute_instr conf instr) rest
  | []            -> conf

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile stmt =
  let rec compile_expr e =
      match e with
      | Language.Expr.Const  c         -> [CONST c]
      | Language.Expr.Var    v         -> [LD v]
      | Language.Expr.Binop (op, l, r) -> compile_expr l @ compile_expr r @ [ BINOP op ] 
    in
    match stmt with
    | Language.Stmt.Read    v       -> [ READ; ST v ]
    | Language.Stmt.Write   e       -> compile_expr e @ [ WRITE ]
    | Language.Stmt.Assign (v, e)   -> compile_expr e @ [ ST v ]
    | Language.Stmt.Seq    (e1, e2) -> compile e1 @ compile e2