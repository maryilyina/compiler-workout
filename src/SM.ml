open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

let ( !? ) n = Language.Expr.Const n
let binop op x y = Language.Expr.Binop (op, x, y)

let sufToOp = function
    | "z" -> let f a = (a = 0) in f
    | "nz" -> let f a = a != 0 in f
    | _ -> failwith "Invalid CJMP suffix"

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env ((control_stack, stack, (s, i, o)) as cfg) prg =
    match prg with
    | [] -> (control_stack, stack, (s, i, o))
    | instr::p -> (match instr with
                    | BINOP op  -> 
                        let y :: x :: stack_rest = stack in 
                        eval env (control_stack, (Value.of_int @@ Expr.to_func op (Value.to_int x) (Value.to_int y)) :: stack_rest, (s, i, o)) p
                    | CONST c ->
                        eval env (control_stack, (Language.Value.of_int c) :: stack, (s, i, o)) p
                    | STRING str -> eval env (control_stack, (Value.of_string str)::stack, (s, i, o)) p
                    | LD x -> 
                        eval env (control_stack, State.eval s x :: stack, (s, i, o)) p
                    | ST x -> 
                        let z :: stack_rest = stack in
                        eval env (control_stack, stack_rest, ((State.update x z s), i, o)) p
                    | STA (x, n) -> let v::ids, stack' = split (n + 1) stack in
                                    let s' = Language.Stmt.update s x v ids in
                                    eval env (control_stack, stack', (s', i, o)) p
                    | LABEL x       -> eval env (control_stack, stack, (s, i, o)) p
                    | JMP   label   -> eval env (control_stack, stack, (s, i, o)) (env#labeled label)
                    | CJMP (znz, l) ->
                        let h :: t = stack in
                        if (Value.to_int h = 0 && znz = "z" || Value.to_int h <> 0 && znz = "nz") then
                            eval env (control_stack, t, (s, i, o)) (env#labeled l)
                        else
                            eval env (control_stack, t, (s, i, o)) p
                    | BEGIN (_, args, locals) -> 
                        let s' = State.enter s (args @ locals) in
                        let take_params = List.map (fun x -> ST x) args in
                        eval env (control_stack, stack, (s', i, o)) (take_params @ p)
                    | END | RET _ -> (
                        match control_stack with
                        | (rest', s') :: control_stack' ->
                            let s'' = Language.State.leave s s' in
                            eval env (control_stack', stack, (s'', i, o)) rest'
                        | _ -> (control_stack, stack, (s, i, o))
                    )
                    | CALL (label, n, is_func) -> if env#is_label label
                        then eval env ((p, s)::control_stack, stack, (s, i, o)) (JMP(label)::p)
                        else eval env (env#builtin cfg label n (not is_func)) p
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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)


let labels_constr = object
    val mutable label_n = 0
    method get_label = label_n <- label_n + 1; "L" ^ string_of_int label_n
end

let rec compile_expr = function
    | Expr.Const n          -> [CONST n]
    | Expr.Var   x          -> [LD x]
    | Language.Expr.String str -> [STRING str]
    | Expr.Binop (op, x, y) -> compile_expr x @ compile_expr y @ [BINOP op]
    | Expr.Call (name, params) -> List.flatten (List.map (compile_expr) (List.rev params)) @ [CALL (name, List.length params, true)]
    | Expr.Array elems      -> let compiled_elems = List.concat (List.map (compile_expr) (List.rev elems)) in
                                compiled_elems @ [CALL ("$array", (List.length compiled_elems), true)]
    | Language.Expr.Elem (e, i) -> compile_expr i @ compile_expr e @ [CALL ("$elem", 2, true)]
    | Language.Expr.Length e -> compile_expr e @ [CALL ("$length", 1, true)]

let rec compile_constr lab = function
    | Stmt.Seq (s1, s2)               -> (let lab1 = labels_constr#get_label in
                                            let p1, used1 = compile_constr lab1 s1 in
                                            let p2, used2 = compile_constr lab s2 in
                                            p1 @ (if used1 then [LABEL lab1] else []) @ p2, used2
                                        )
    | Stmt.Assign (x, is, e)          -> (match is with
                                            | [] -> (compile_expr e @ [ST x]), false
                                            | is -> let compiled_is = List.fold_left
                                                        (fun p id -> p @ (compile_expr id)) [] (List.rev is) in
                                                        compiled_is @ compile_expr e @ [STA (x, List.length is)], false)
    | Stmt.Skip                       -> [], false
    | Stmt.If (what, first, second)   -> (let else_label = labels_constr#get_label in
                                            let first_body, used1 = compile_constr lab first in
                                            let second_body, used2 = compile_constr lab second in
                                            compile_expr what @ [CJMP ("z", else_label)]
                                            @ first_body @ (if used1 then [] else [JMP lab]) @ [LABEL else_label]
                                            @ second_body @ (if used2 then [] else [JMP lab]), true
                                            )
    | Stmt.While (what, body)            -> (let condition_label = labels_constr#get_label in
                                            let loop_label = labels_constr#get_label in
                                            let main_body, _ = compile_constr condition_label body in
                                            [JMP condition_label; LABEL loop_label] @ main_body @
                                            [LABEL condition_label] @ compile_expr what @ [CJMP ("nz", loop_label)], false
                                        )
    | Stmt.Repeat (body, what)           -> (let loop_label = labels_constr#get_label in
                                            let condition_label = labels_constr#get_label in
                                            let repeat_body, used = compile_constr loop_label body in
                                            [LABEL loop_label] @ repeat_body @ (if used then [LABEL condition_label] else []) @ compile_expr what @ [CJMP ("z", loop_label)], false
                                        )
    | Stmt.Call (name, params)        -> List.flatten (List.map (compile_expr) (List.rev params)) @ [CALL (name, List.length params, false)], false
    | Stmt.Return e                   -> (match e with Some x -> (compile_expr x) @ [RET true] | None -> [RET false]), false

let compile_prog prog =
    let label = labels_constr#get_label in
    let prg, used = compile_constr label prog in
    prg @ (if used then [LABEL label] else [])

let rec compile (defs, main) =
  let main_compiled = compile_prog main in
  let defs_compiled = 
      (let compile_definition (name, (params, locals, body)) = 
        (let compiled = compile_prog body in
        [LABEL name; BEGIN (name, params, locals)] @ compiled @ [END]) in
      List.flatten (List.map compile_definition defs)) in
  main_compiled @ [END] @ defs_compiled