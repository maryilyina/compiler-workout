open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *) 



let rec eval env conf prg = match prg with
  | [] -> conf
(*
  | _  -> (
    let (control_stack, stack, (s, i, o)) = conf in
    let instr :: rest = prg in 
    match instr with 
      | LABEL x            -> eval env conf rest
      | JMP   label        -> eval env conf (env#labeled label)
      | CJMP  (cond, label) -> (
        let z :: stack_rest = stack in match cond with 
          | "z"  -> (
                      if z <> 0 then eval env (control_stack, stack_rest, (s, i, o)) rest 
                      else eval env (control_stack, stack_rest, (s, i, o)) (env#labeled label))
          | "nz" -> (
                      if z <> 0 then eval env (control_stack, stack_rest, (s, i, o)) (env#labeled label) 
                      else eval env (control_stack, stack_rest, (s, i, o)) rest )
      )
      | BINOP op -> 
      let y :: x :: stack_rest = stack in 
      eval env (control_stack, (Language.Expr.to_func op x y) :: stack_rest, (s, i, o)) rest

      | CONST c -> 
          eval env (control_stack, c :: stack, (s, i, o)) rest
      | READ -> 
          let z :: stack_rest = i in
          eval env (control_stack, z :: stack, (s, stack_rest, o)) rest
      | WRITE -> 
          let z :: stack_rest = stack in
          eval env (control_stack, stack_rest, (s, i, o @ [z])) rest
      | LD x -> eval env (control_stack, (s x) :: stack, (s, i, o)) rest
      | ST x -> 
          let z :: stack_rest = stack in
          eval env (control_stack, stack_rest, ((Language.State.update x z s), i, o)) rest

      | _ -> eval env (execute_instr conf instr) rest
    )
    *)

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

let lables_constr = object
    val mutable label_n = 0
    method get_label = label_n <- label_n + 1; "L" ^ string_of_int label_n
end

let rec compile_expr e = match e with
    | Expr.Var   x -> [LD x]
    | Expr.Const x -> [CONST x]
    | Expr.Binop (op, e1, e2) -> compile_expr e1 @ compile_expr e2 @ [BINOP op]

let rec compile_constr p after_label = match p with
    | Stmt.Read  x        -> ([READ; ST x]), false
    | Stmt.Write e        -> (compile_expr e @ [WRITE]),   false
    | Stmt.Assign (x, e)  -> (compile_expr e @ [ST x]), false
    | Stmt.Seq    (a, b)  ->  let label = lables_constr#get_label in
                              let (prg_a, used_a) = compile_constr a label in
                              let (prg_b, used_b) = compile_constr b after_label in
                              prg_a @ (if used_a then [LABEL label] else []) @ prg_b, used_b
    | Stmt.Skip -> [], false
    
    | Stmt.If (what, first, second) ->
        let else_label = lables_constr#get_label in
        let (first_body,  used1) = compile_constr first  after_label in
        let (second_body, used2) = compile_constr second after_label in
        (compile_expr what) @ [CJMP ("z", else_label)] @
        first_body  @ (if used1 then [] else [JMP after_label]) @ [LABEL else_label] @
        second_body @ (if used2 then [] else [JMP after_label]), true
    
    | Stmt.While (what, body) -> 
        let condition_label = lables_constr#get_label in
        let loop_label      = lables_constr#get_label in
        let (main_body, _) = compile_constr body condition_label in
        let condition = compile_expr what in
        [JMP condition_label; LABEL loop_label] @
        main_body @ [LABEL condition_label] @ condition @ [CJMP ("nz", loop_label)], false
    
    | Stmt.RepeatUntil (body, what) -> 
        let loop_label = lables_constr#get_label in
        let (repeatBody, _) = compile_constr body after_label in
        ([LABEL loop_label] @ repeatBody @ compile_expr what @ [CJMP ("z", loop_label)]), false
  

let rec compile p = let label = lables_constr#get_label in
                    let prg, used = compile_constr p label in
                    prg @ (if used then [LABEL label] else [])
