(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

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
    *)                                                       
    let rec eval env ((st, i, o, r) as conf) expr = failwith "Not implemented"
         
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
      | x:IDENT   {Var x}
      | -"(" parse -")"
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
    let rec eval env (s, i, o) statement = match statement with
        | Read x -> 
            (let head::tail = i in
            State.update x head s, tail, o)
        | Write e       -> (s, i, o @ [Expr.eval s e])
        | Assign (x, e) -> (State.update x (Expr.eval s e) s, i, o) 
        | Seq    (a, b) -> eval env (eval env (s, i, o) a) b  
        | If (what, first, second)  -> 
              eval env (s, i, o) 
              (if Expr.eval s what == 0 then second else first)
        | While (what, body)  ->
            (if Expr.eval s what == 0 then (s, i, o)
            else 
              let repeatition = While (what, body) in 
              eval env (eval env (s, i, o) body) repeatition)
        | RepeatUntil (body, what) ->
            let repeatition = While (Expr.Binop ("==", what, Expr.Const 0), body) in
              eval env (eval env (s, i, o) body) repeatition
        | Skip -> (s, i, o)
        (*
        | Call (func, param_exprs)    -> 
            let (args, locals, body) = env#definition func in
            let params = List.map (Expr.eval s) param_exprs in
            let upd s x v = State.update x v s in

            let s' = State.push_scope s (args @ locals) in
            let folded_s' = List.fold_left2 upd s' args params in
            let (s'', i, o) = eval env (folded_s', i, o) body in
            (State.drop_scope s'' s, i, o)
            *)
        
    (* Statement parser *)
    ostap (

      parse: empty {failwith "Not yet implemented"}
      (*call_statement:
        funct:IDENT "(" args:( !(Expr.parse) )* ")" { Call (funct, args) };

      statement: 
          "read"    "("   x:IDENT        ")"  { Read   x    }
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
        | "repeat" body:!(parse) "until" what:!(Expr.parse) { RepeatUntil (body, what) }
        | "for" what:!(parse) "," cond:!(Expr.parse) "," step:!(parse) "do" body:!(parse)
          "od" { Seq (what, While (cond, Seq (body, step))) }
        | "skip" { Skip }
        | call:call_statement { call };

      parse: line:statement ";" tail:parse { Seq (line, tail) } | statement*)
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
                                          
      parse: empty {failwith "Not yet implemented"}
      (*
        "fun" funct:IDENT "(" args:(IDENT)* ")"
        locals:(%"local" (IDENT) ?
        "{" body:!(Stmt.parse) "}"
        { funct, (args, get_or_default [] locals, body) }*)
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
