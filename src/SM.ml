open GT       
open Language
open List
       
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
        
let check_jump cond value = 
  match cond with
  | "z" -> Value.to_int value = 0
  | "nz" -> Value.to_int value <> 0

let rec mapArgs accumulator args stack = match args, stack with
  | [], _ -> List.rev accumulator, stack
  | a::tlArgs, s::tlStack -> mapArgs ((a, s)::accumulator) tlArgs tlStack

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf)  = function
  | [] -> conf
| insn :: prg' ->
     (match insn with
      | BINOP op -> let y::x::stack' = stack in eval env (cstack, (Value.of_int (Expr.evalBinaryOperation op (Value.to_int x) (Value.to_int y))) :: stack', c) prg'
      | CONST i  -> eval env (cstack, (Value.of_int i)::stack, c) prg'
      | STRING s -> eval env (cstack, (Value.of_string s)::stack, c) prg'
      | LD x     -> eval env (cstack, State.eval st x :: stack, c) prg'
      | ST x     -> let z::stack' = stack in eval env (cstack, stack', (State.update x z st, i, o)) prg'
      | STA (x, n) -> let v::ind, stack' = split (n + 1) stack in eval env (cstack, stack', (Language.Stmt.update st x v (List.rev ind), i, o)) prg'
      | LABEL s  -> eval env conf prg'
      | JMP name -> eval env conf (env#labeled name)
      | CJMP (condition, name) -> eval env (cstack, tl stack, c) (if (check_jump condition (hd stack)) then (env#labeled name) else prg')
      | CALL (f, n, p) -> if env#is_label f then eval env ((prg', st)::cstack, stack, c) (env#labeled f) else eval env (env#builtin conf f n p) prg'
      | BEGIN (_, args, locals) -> let mappedArgs, newStack = mapArgs [] args stack 
        in eval env (cstack, newStack, (List.fold_left (fun s (x, v) -> State.update x v s) (State.enter st (args @ locals)) mappedArgs, i, o)) prg'
      | END | RET _ -> (match cstack with
        | (prg', st')::cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) prg'
        | [] -> conf)
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
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
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
class labels = 
  object (self)
    val counter = 0
    method new_label = "label_" ^ string_of_int counter, {<counter = counter + 1>}
  end

let make_label name = "L" ^ name

let rec compile_labels labels =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.String s         -> [STRING s]
  | Expr.Array arr        -> List.flatten (List.map expr arr) @ [CALL ("$array", List.length arr, false)]
  | Expr.Elem (arr, i)    -> expr arr @ expr i @ [CALL ("$elem", 2, false)]
  | Expr.Length t         -> expr t @ [CALL ("$length", 1, false)]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (f, args)   -> compile_call f args false
  and compile_call f args p = let compile_args = List.map expr (List.rev args) in
    let cArgs = List.concat compile_args in
    cArgs @ [CALL (make_label f, List.length args, p)]
  in
  function
  | Stmt.Seq (s1, s2)  -> 
    let labels1, res1 = compile_labels labels s1 in
    let labels2, res2 = compile_labels labels1 s2 in
    labels2, res1 @ res2
  | Stmt.Assign (x, [], e) -> labels, expr e @ [ST x]
  | Stmt.Assign (x, is, e) -> labels, List.flatten (List.map expr (is @ [e])) @ [STA (x, List.length is)]
  | Stmt.Skip          -> labels, []
  | Stmt.If (condition, argIF, argElse) ->
    let cCond = expr condition in
    let jumpElse, labels1 = labels#new_label in
    let jumpEndIf, labels2 = labels1#new_label in
    let labels3, compiledIf = compile_labels labels2 argIF in
    let labels4, compiledElse = compile_labels labels3 argElse in
    labels4, cCond @ [CJMP ("z", jumpElse)] @ compiledIf @ [JMP jumpEndIf] @ [LABEL jumpElse] @ compiledElse @ [LABEL jumpEndIf]
  | Stmt.While (condition, loop) ->
    let cCond = expr condition in
    let labelBegin, labels1 = labels#new_label in
    let labelEnd, labels2 = labels1#new_label in
    let labels3, compile_loop = compile_labels labels2 loop in
    labels3, [LABEL labelBegin] @ cCond @ [CJMP ("z", labelEnd)] @ compile_loop @ [JMP labelBegin] @ [LABEL labelEnd] 
  | Stmt.Repeat (loop, condition) ->
    let cCond = expr condition in
    let labelBegin, labels1 = labels#new_label in
    let labels2, compile_loop = compile_labels labels1 loop in
    labels2, [LABEL labelBegin] @ compile_loop @ cCond @ [CJMP ("z", labelBegin)]
  | Stmt.Call (f, args) -> labels, compile_call f args true
  | Stmt.Return res -> labels, (match res with None -> [] | Some v -> expr v) @ [RET (res <> None)]

let compile_func labels (name, (args, locals, body)) = let endLabel, labels1 = labels#new_label in
  let labels2, compiledFunction = compile_labels labels1 body in
  labels2, [LABEL name; BEGIN (name, args, locals)] @ compiledFunction @ [LABEL endLabel; END]

let compile_all labels defs = 
  List.fold_left (fun (labels, allDefsCode) (name, others) -> let labels1, singleCode = compile_func labels (make_label name, others) in labels1, singleCode::allDefsCode)
    (labels, []) defs
let compile (defs, p) = let endLabel, labels = (new labels)#new_label in
  let labels1, compiledProgram = compile_labels labels p in 
  let labels2, defs = compile_all labels1 defs in
  (compiledProgram @ [LABEL endLabel]) @ [END] @ (List.concat defs)
