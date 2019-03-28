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
(* conditional jump                *) | CJMP  of string * string with show
                                                   
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
  | LABEL _ -> (stack, (s, i, o))

let rec eval env conf prg = match prg with
  | [] -> conf
  | _  -> (
    let instr :: rest = prg in 
    match instr with 
      (*| LABEL x -> eval env conf rest*)
      | JMP   label        -> eval env conf (env#labeled label)
      | CJMP  (cond, label) -> (
        let (stack, state) = conf in
        let z :: stack_rest = stack in
          eval env (stack_rest, state) (
            if (cond == "z" && z <> 0 || cond == "znz" && z == 0) then rest else (env#labeled label)))
      | _ -> eval env (execute_instr conf instr) rest
    )

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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
class unique_labels =
  object
    val label_n = 0
    method get_label = {< label_n = label_n + 1 >}, "L" ^ string_of_int label_n
  end

let rec compile_expr e = match e with
    | Expr.Var   x -> [LD x]
    | Expr.Const x -> [CONST x]
    | Expr.Binop (op, e1, e2) -> compile_expr e1 @ compile_expr e2 @ [BINOP op]

let rec compile_constr id p after_label = match p with
    | Stmt.Read  x        -> ([READ; ST x]), false
    | Stmt.Write e        -> (compile_expr e @ [WRITE]),   false
    | Stmt.Assign (x, e)  -> (compile_expr e @ [ST x]), false
    | Stmt.Seq    (a, b)  ->  let (id, label) = id#get_label in
                              let (prg_a, used_a) = compile_constr id a label in
                              let (prg_b, used_b) = compile_constr id b after_label in
                              prg_a @ (if used_a then [LABEL label] else []) @ prg_b, used_b
    | Stmt.Skip -> [], false
    | Stmt.If (what, first, second) ->
        let (id, else_label) = id#get_label in
        let (first_body,  used1) = compile_constr id first  after_label in
        let (second_body, used2) = compile_constr id second after_label in
        (compile_expr what) @ [CJMP ("z", else_label)] @
        first_body  @ (if used1 then [] else [JMP after_label]) @ [LABEL else_label] @
        second_body @ (if used2 then [] else [JMP after_label]), true
    | Stmt.While (what, body) -> 
        let (id, before_label)    = id#get_label in
        let (id, condition_label) = id#get_label in
        let (main_body, _) = compile_constr id body condition_label in
        let condition = compile_expr what in
        [JMP condition_label; LABEL before_label] @
        main_body @ [LABEL condition_label] @ condition @ [CJMP ("nz", before_label)], false
    | Stmt.RepeatUntil (body, what) -> 
        let (p::rest, _) = (
          let while_cond = Expr.Binop ("==", what, Expr.Const 0) in
          compile_constr id (Language.Stmt.While (while_cond, body)) after_label
          ) in rest, false

let rec compile p = let id, label = (new unique_labels)#get_label in
                    let prg, used = compile_constr id p label in
                    prg @ (if used then [LABEL label] else [])