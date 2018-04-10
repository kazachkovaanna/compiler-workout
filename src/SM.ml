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

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | JMP name :: _ -> eval env conf (env#labeled name)
  | CJMP (cond, name) :: prg' -> 
    (match stack with
      | (x::new_stack) -> 
          (if (cond = "z" && x = 0) || (cond = "nz" && x <> 0) 
            then eval env (cstack, new_stack, c) (env#labeled name)
            else eval env (cstack, new_stack, c) prg'
          )
      | _ -> failwith "Empty stack"
    )
  | CALL name :: prg_next ->  eval env ((prg_next, st)::cstack, stack, c)(env#labeled name)
  | END :: _-> let (prg_prev, st_prev)::cstack_new = cstack in
                eval env (cstack_new, stack, (State.leave st st_prev, i, o)) prg_prev
  | insn :: prg' ->
    let newConfig = match insn with
        | BINOP op -> let y::x::stack' = stack in (cstack, Expr.to_func_renamed op x y :: stack', c)
        | READ     -> let z::i'        = i     in (cstack, z::stack, (st, i', o))
        | WRITE    -> let z::stack'    = stack in (cstack, stack', (st, i, o @ [z]))
        | CONST i  -> (cstack, i::stack, c)
        | LD x     -> (cstack, State.eval st x :: stack, c)
        | ST x     -> let z::stack' = stack in (cstack, stack', (State.update x z st, i, o))
        | LABEL name -> conf
        | BEGIN (p, l) -> let st_enter = State.enter st (p @ l) in
                let stack_to_st = fun p (st, x::stack_next) ->  (State.update p x st, stack_next) in
                let (st_enter, _) = List.fold_right stack_to_st
                p (st_enter, stack) in
                (cstack, stack, (st_enter, i, o))
        | _ -> failwith "Smth wrong!"
    in eval env newConfig prg'
 

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
let createLabel number = "L_" ^ (string_of_int number)

let compile (defs, p) =
  let rec expr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  let rec compileStatement count = function  
    | Stmt.Read x ->  (count, [READ; ST x])
    | Stmt.Write e -> (count, expr e @ [WRITE])
    | Stmt.Assign (x, e) -> (count, expr e @ [ST x])
    | Stmt.Skip -> (count, [])
    | Stmt.Seq (firstStatement, secondStatement) -> 
        let (firstCondition, fistBody) = compileStatement count firstStatement in
        let (secondStatement, secondBody) = compileStatement firstCondition secondStatement in
        (secondStatement, fistBody @ secondBody)                                     
    | Stmt.If (cond, firstStatement, secondStatement) -> 
        let firstCondition, fistBody = compileStatement count firstStatement in
        let thenLabel = createLabel firstCondition in
        let secondStatement, secondBody = compileStatement (firstCondition+1) secondStatement in
        let elseLabel = createLabel secondStatement in
        (secondStatement+1, expr cond @ [CJMP ("z", thenLabel)] @ fistBody @ [JMP elseLabel; LABEL thenLabel] @ secondBody @ [LABEL elseLabel])                        
    | Stmt.While (cond, st) -> 
        let loopLabel = createLabel count in
        let (firstCondition, fistBody) = compileStatement (count+1) st in
        let checkLabel = createLabel firstCondition in
        (firstCondition+1, [JMP checkLabel; LABEL loopLabel] @ fistBody @ [LABEL checkLabel] @ expr cond @ [CJMP ("nz", loopLabel)])
    | Stmt.Repeat (st, cond) ->  
        let loopLabel = createLabel count in
        let (firstCondition, fistBody) = compileStatement (count+1) st in
        (firstCondition, [LABEL loopLabel] @ fistBody @ expr cond @ [CJMP ("z", loopLabel)])
    | Stmt.Call (name, args) -> let progArgs = List.concat @@ List.map expr args in
        (count, progArgs @ [CALL ("L_" ^ name)])
  in 
  let compileDefinition countR (name, (params, locals, body)) =
    let (firstCondition, progFunc) = compileStatement countR body in
    (firstCondition, [LABEL name; BEGIN (params, locals)] @ progFunc @ [END])
  in
  let startCount = 0
  in
  let countStart, defsProg = List.fold_left
      (fun (counter, prgs)(name, configur) -> 
          let (countZ, progNew) = compileDefinition counter ("L_" ^ name, configur) 
          in (countZ, progNew::prgs))
      (startCount, [])
      defs
  in
  let (_, prg) = compileStatement countStart p in
  let mainLabel = "L_main"
  in ([JMP mainLabel] @ (List.concat defsProg) @ [LABEL mainLabel] @ prg)
