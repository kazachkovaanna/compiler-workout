open GT       
       
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
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval config prog =
	match prog with
	| [] -> config
	|instruction::tail -> (
		match config, instruction with
		| (y::x::stack, tm_conf), BINOP operation -> 
			let value = Syntax.Expr.evalBinaryOperation operation x y in
			eval (value::stack, tm_conf) tail
		| (stack, tm_conf), CONST value ->
			eval (value::stack, tm_conf) tail
		| (stack, (st, z::input, output)), READ -> 
			eval (z::stack, (st, input, output)) tail
		| (z::stack, (st, input, output)), WRITE -> 
			eval (stack, (st, input, output @ [z])) tail
		| (stack, (st, input, output)), LD x -> 
			let value = st x in
			eval (value::stack, (st, input, output)) tail
		| (z::stack, (st, input, output)), ST x -> 
			let stt = Syntax.Expr.update x z st in
			eval (stack, (stt, input, output)) tail
	)

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compileExpression expr = 
	match expr with
	| Syntax.Expr.Const c -> [CONST c]
	| Syntax.Expr.Var x -> [LD x]
	| Syntax.Expr.Binop (operation, leftOperation, rightOperation) -> compileExpression leftOperation @ compileExpression rightOperation @ [BINOP operation]

let rec compile statement = 
	match statement with
	| Syntax.Stmt.Assign (x, expr) -> compileExpression expr @ [ST x]
	| Syntax.Stmt.Read x -> [READ; ST x]
	| Syntax.Stmt.Write expr -> compileExpression expr @ [WRITE]
	| Syntax.Stmt.Seq (leftStatement, rightStatement) -> compile leftStatement @ compile rightStatement
