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
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let check_jump cond hd = 
  match cond with
  | "z" -> hd == 0
  | "nz" -> hd <> 0

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf)  = function
  | [] -> conf
  | insn :: ins_t ->
    eval env
		(match insn with
		| CONST var -> 
      (cstack, var :: stack, c)
		| READ -> 
      (cstack, (List.hd i) :: stack, (st, List.tl i, o))
		| WRITE -> 
      (cstack, List.tl stack, (st, i, o @ [List.hd stack]))
		| LD var -> 
      (cstack, State.eval st var :: stack, c)
		| ST x ->
      (cstack, List.tl stack, (State.update x (List.hd stack) st, i, o)) 
		| BINOP oper -> 
      let y :: x :: t = stack in
      let binop = Expr.evalBinaryOperation oper x y in
      (cstack, binop :: t, c)
		| LABEL _ -> 
      (cstack, stack, c)
		| JMP l -> 
      eval env conf (env#labeled l)
		| CJMP (cond, l)  -> 
		  if (check_jump cond (List.hd stack)) then 
        eval env (cstack, stack, c) (env#labeled l) 
        else eval env (cstack, stack, c) ins_t
		| CALL func -> 
      let cstack' = ((ins_t, st)::cstack) in 
      eval env (cstack', stack, c) (env#labeled func)
		| BEGIN (args, loc_vars) ->(
		  let bind ((v :: stack), state) x = (stack, State.update x v state) in
      let (stack', st') = List.fold_left bind (stack, State.enter st (args @ loc_vars)) args in
      eval env (cstack, stack', (st', i, o)) ins_t
      )
		| END ->
		  match cstack with
		  | (pr, s)::cstack' -> 
        eval env (cstack', stack, (Language.State.leave st s, i, o)) pr
		  | [] -> conf
    ) ins_t

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
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

 let labels =
  object
    val mutable count = 0
    method generate =
        count <- count + 1;
        "label_" ^ string_of_int count
    end

let rec compile_expr expr =
    match expr with
    | Expr.Const c -> 
      [CONST c]
    | Expr.Var v -> 
      [LD v]
    | Expr.Binop (op, l, r) -> 
      (compile_expr l) @ (compile_expr r) @ [BINOP op]
    | Expr.Call (fun_name, args) -> 
      List.concat (List.map compile_expr args) @ [CALL fun_name]

let rec compile_stmt stmt =
    match stmt with
    | Stmt.Read var -> 
      [READ;ST var]
    | Stmt.Write expr -> 
      compile_expr expr @ [WRITE]
    | Stmt.Assign (var, expr) -> 
      compile_expr expr @ [ST var]
    | Stmt.Seq (st1, st2) -> 
      compile_stmt st1 @ compile_stmt st2
    | Stmt.Skip -> []
    | Stmt.If (cond, l, r) ->
      let else_begin = labels#generate in
      let endif_lbl = labels#generate in
      (compile_expr cond) @ 
      [CJMP ("z", else_begin)] @ 
      (compile_stmt l)@ 
      [JMP endif_lbl; LABEL else_begin] @ 
      (compile_stmt r) @ 
      [LABEL endif_lbl]
    | Stmt.While (cond, body) ->
      let begin_l = labels#generate in
      let end_l = labels#generate in
      [LABEL begin_l] @ 
      (compile_expr cond) @ 
      [CJMP ("z", end_l)] @ 
      (compile_stmt body) @ 
      [JMP begin_l; LABEL end_l]
    | Stmt.Repeat (body, cond) ->
      let begin_l = labels#generate in
      [LABEL begin_l] @ 
      (compile_stmt body) @ 
      (compile_expr cond) @ 
      [CJMP ("z", begin_l)]
    | Stmt.Call (f_name, args) -> 
      List.concat (List.map compile_expr args) @ [CALL f_name]
    | Stmt.Return pos_val -> 
      match pos_val with Some v -> 
      (compile_expr v) @ [END] 
    | _ -> [END]

let compile_definition (f_name, (args, local_vars, body)) = 
[LABEL f_name; BEGIN (args, local_vars)] @ 
(compile_stmt body) @ 
[END]

let rec compile (defs, program) =
[LABEL "main"] @ (compile_stmt program) @ [END] @ (List.concat (List.map compile_definition defs))