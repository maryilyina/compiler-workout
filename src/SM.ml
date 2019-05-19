open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
(* drop values from stack and jmp  *) | DROPJMP of string * int with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine confuration: control stack, stack and confuration from statement
   interpreter
*)
type conf = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter
     val eval : env -> conf -> prg -> conf
   Takes an environment, a confuration and a program, and returns a confuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let rec eval env ((control_stack, stack, (s, i, o)) as conf) prg =
  match prg with
    | [] -> conf
    | instr::rest -> (
        let eval_with_new_stack st = eval env (control_stack, st, (s, i, o)) rest in
        match instr with
          | BINOP op  -> 
              let y::x::stack_rest = stack in 
              eval_with_new_stack ((Value.of_int @@ Expr.to_func op (Value.to_int x) (Value.to_int y))::stack_rest)
          | CONST c ->
              eval_with_new_stack ((Value.of_int c)::stack)
          | STRING str -> 
              eval_with_new_stack ((Value.of_string (Bytes.of_string str))::stack)
          | SEXP (tag, count) -> 
            let values, rest_stack = split count stack in 
            eval_with_new_stack ((Value.sexp tag @@ (List.rev values))::rest_stack)
          | LD x -> 
              eval env (control_stack, State.eval s x::stack, (s, i, o)) rest
          | ST x -> 
              let z::stack_rest = stack in
              eval env (control_stack, stack_rest, ((State.update x z s), i, o)) rest
          | STA (x, n) -> let v::ids, stack' = split (n + 1) stack in
              let s' = Stmt.update s x v (List.rev ids) in
              eval env (control_stack, stack', (s', i, o)) rest
          | LABEL x       -> eval env conf rest
          | JMP   label   -> eval env conf (env#labeled label)
          | CJMP (znz, l) ->
              let h::stack_rest = stack in
              eval env (control_stack, stack_rest, (s, i, o)) (
                if (Value.to_int h = 0 && znz = "z" || Value.to_int h <> 0 && znz = "nz") 
                  then (env#labeled l)
                  else rest
              )
          | BEGIN (_, arg_names, local_names) -> 
            let fun_s = State.enter s (arg_names @ local_names) in
            let updated_s, updated_stack = 
              List.fold_left 
                (fun (s, value::rest) name -> (State.update name value s, rest))
                (fun_s, stack) (List.rev arg_names) in
            eval env (control_stack, updated_stack, (updated_s, i, o)) rest
          | END | RET _ -> (
              match control_stack with
              | (rest', s')::control_stack' ->
                  let s'' = State.leave s s' in
                  eval env (control_stack', stack, (s'', i, o)) rest'
              | _ -> conf)
          | CALL (name, args_count, is_procedure) -> 
            if env#is_label name 
              then eval env ((rest, s)::control_stack, stack, (s, i, o)) (env#labeled name)
              else eval env (env#builtin (control_stack, stack, (s, i, o)) name args_count (is_procedure)) rest 
          | DROPJMP (l, depth) -> 
            let z::stack = stack in
            if Value.to_int z = 0 
              then let (_,  jmp_stack) = split depth stack in eval env (control_stack, jmp_stack, (s, i, o)) (env#labeled l)
              else eval env (control_stack, stack, (s, i, o)) rest
          | LEAVE -> eval env (control_stack, stack, (State.drop s, i, o)) rest
          | ENTER args ->
            let values, stack = split (List.length args) stack in
            let scope = List.fold_left (fun st (name, value) -> State.bind name value st) State.undefined (List.combine args values) in
            let s = (State.push s scope args) in
            eval env (control_stack, stack, (s, i, o)) rest
          | DROP -> eval_with_new_stack (List.tl stack)
          | DUP -> eval_with_new_stack ((List.hd stack)::stack)
          | SWAP ->
            let x::y::stack_rest = stack in 
            eval_with_new_stack (y::x::stack_rest)
          | TAG t ->
            let x::stack_rest = stack in
            let res = match x with
              | Value.Sexp (t', _) -> if (t = t') then 1 else 0
              | _ -> 0 in
            eval_with_new_stack ((Value.of_int res)::stack_rest)
          | _ -> failwith "Unknown instruction")

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l)::tl -> make_map (M.add l tl m) tl
  | _::tl         -> make_map m tl
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
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (*Printf.printf "Builtin:\n";*)
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
    method get_label = 
        label_n <- label_n + 1; 
        "L" ^ string_of_int label_n
end


let rec compile_call name args is_procedure = 
  let compiled_args = List.flatten @@ List.map compile_expr args in
  compiled_args @ [CALL (name, List.length args, is_procedure)]

and compile_expr = function
    | Expr.Const n            -> [CONST n]
    | Expr.Var x              -> [LD x]
    | Expr.String str         -> [STRING str]
    | Expr.Array elems        -> 
        let compiled_elems = List.flatten (List.map compile_expr elems) in
        compiled_elems @ [CALL (".array", (List.length compiled_elems), false)]
    | Expr.Sexp (name, exprs) ->  
        let compiled_exprs = List.flatten (List.map compile_expr exprs) in
        compiled_exprs @ [SEXP (name, List.length exprs)]
    | Expr.Binop (op, x, y)   -> compile_expr x @ compile_expr y @ [BINOP op]
    | Expr.Elem (arr, idx)    -> compile_expr arr @ compile_expr idx @ [CALL (".elem", 2, false)]
    | Expr.Length arr         -> compile_expr arr @ [CALL (".length", 1, false)]
    | Expr.Call (name, args)  -> compile_call name args false
  
and make_bindings pattern =
  let rec inner p = match p with
    | Stmt.Pattern.Wildcard -> []
    | Stmt.Pattern.Ident var -> [[]]
    | Stmt.Pattern.Sexp (_, exprs) -> 
      let next i x = List.map (fun arr -> i::arr) (inner x) in List.flatten (List.mapi next exprs)
  in
  let elem i = [CONST i; CALL (".elem", 2, false)] in
  let extract_bind_value path = [DUP] @ (List.flatten (List.map elem path)) @ [SWAP] in
  List.flatten (List.map extract_bind_value (List.rev (inner pattern)))

and compile_simple_branch pattern stmt next_label lab =
  let pattern_prg, p_used = compile_pattern pattern next_label 0 in
  let stmt_prg, s_used = compile_constr lab (Stmt.Seq (stmt, Stmt.Leave)) in
  pattern_prg @ make_bindings pattern @ [DROP; ENTER (List.rev (Stmt.Pattern.vars pattern))] @ stmt_prg, p_used, s_used

and compile_pattern pattern lab depth = 
  match pattern with
    | Stmt.Pattern.Wildcard -> [DROP], false
    | Stmt.Pattern.Ident _ -> [DROP], false
    | Stmt.Pattern.Sexp (name, exprs) ->
      let compile_subpattern i pattern = 
        let inner_prg = match pattern with
        | Stmt.Pattern.Sexp (_, ps) -> 
          if List.length ps > 0 
            then [DUP] @ fst (compile_pattern pattern lab (depth + 1)) @ [DROP]
            else fst (compile_pattern pattern lab depth)
        | _ -> fst (compile_pattern pattern lab depth) 
        in  
        [DUP; CONST i; CALL (".elem", 2, false)] @ inner_prg in 
      let prg = List.flatten (List.mapi compile_subpattern exprs) in
      [TAG name] @ [DROPJMP (lab, depth)] @ prg, true 

and compile_constr lab = function
    | Stmt.Seq (s1, s2)               -> (let lab1 = labels_constr#get_label in
                                          let p1, used1 = compile_constr lab1 s1 in
                                          let p2, used2 = compile_constr lab s2 in
                                          p1 @ (if used1 then [LABEL lab1] else []) @ p2, used2
                                        )
    | Stmt.Assign (name, ids, e)      -> (match ids with
                                            | [] -> compile_expr e @ [ST name], false
                                            | ids -> 
                                                let compiled_ids = List.fold_left (fun comp e -> comp @ (compile_expr e)) [] ids in
                                                compiled_ids @ compile_expr e @ [STA (name, List.length ids)], false)  
    | Stmt.Skip                       -> [], false
    | Stmt.If (what, first, second)   -> (let else_label = labels_constr#get_label in
                                          let first_body,  used1 = compile_constr lab first in
                                          let second_body, used2 = compile_constr lab second in
                                          compile_expr what @ [CJMP ("z", else_label)]
                                          @ first_body  @ (if used1 then [] else [JMP lab]) @ [LABEL else_label]
                                          @ second_body @ (if used2 then [] else [JMP lab]), true
                                        )
    | Stmt.While (what, body)         -> (let condition_label = labels_constr#get_label in
                                          let loop_label = labels_constr#get_label in
                                          let main_body, _ = compile_constr condition_label body in
                                          [JMP condition_label; LABEL loop_label] @ main_body @
                                          [LABEL condition_label] @ compile_expr what @ [CJMP ("nz", loop_label)], false
                                        )
    | Stmt.Repeat (body, what)        -> (let loop_label = labels_constr#get_label in
                                          let condition_label = labels_constr#get_label in
                                          let repeat_body, used = compile_constr loop_label body in
                                          [LABEL loop_label] @ repeat_body @ (if used then [LABEL condition_label] else []) @ compile_expr what @ [CJMP ("z", loop_label)], false
                                        )
    | Stmt.Return what                -> (match what with 
                                          Some x -> (compile_expr x) @ [RET true] 
                                          | None -> [RET false]), false
    | Stmt.Call (name, args) -> compile_call name args true, false
    | Stmt.Leave -> [LEAVE], false
    | Stmt.Case (what, [pattern, body])-> let br_prg, p_used, s_used = compile_simple_branch pattern body lab lab in 
                                          compile_expr what @ [DUP] @ br_prg, p_used || s_used 
    | Stmt.Case (what, branches)       -> let n = List.length branches - 1 in
                                          let compile_branch_fold (prev_label, i, prg) (pattern, p_stmt) =
                                            let has_next = (i != n) in
                                            let next_label = if has_next then labels_constr#get_label else lab in
                                            let label_prg = match prev_label with Some x -> [LABEL x; DUP] | None -> [] in
                                            let br_prg, _, _ = compile_simple_branch pattern p_stmt next_label lab in
                                            let cur_prg = label_prg @ br_prg @ (if has_next then [JMP lab] else []) in
                                            Some next_label, i + 1, cur_prg::prg in
                                          let _, _, prg = List.fold_left compile_branch_fold (None, 0, []) branches in
                                          compile_expr what @ [DUP] @ List.flatten @@ List.rev prg, true
                                        

and compile_stmt stmt =
  let lab = labels_constr#get_label in
  let prg, used = compile_constr lab stmt in
  prg @ (if used then [LABEL lab] else []) 

and compile_defs defs =
  List.fold_left 
  (fun prev (name, (args, locals, body)) -> 
    let compiled_body = compile_stmt body in 
    prev @ [LABEL name] @ [BEGIN (name, args, locals)] @ compiled_body @ [END]
  )
  []
  defs

and compile (defs, stmt) = 
  let compiled_stmt = compile_stmt stmt in
  let compiled_defs = compile_defs defs in
compiled_stmt @ [END] @ compiled_defs