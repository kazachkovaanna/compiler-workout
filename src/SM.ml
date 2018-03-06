open GT       
open Language
       
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
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval config prog =
	match prog with
	| [] -> config
	|instruction::tail -> (
		match config, instruction with
		| (y::x::stack, conf), BINOP operation -> 
			let value = Language.Expr.evalBinaryOperation operation x y in
			eval (value::stack, conf) tail
		| (stack, conf), CONST value ->
			eval (value::stack, conf) tail
		| (stack, (stmnt, z::input, output)), READ -> 
			eval (z::stack, (stmnt, input, output)) tail
		| (z::stack, (stmnt, input, output)), WRITE -> 
			eval (stack, (stmnt, input, output @ [z])) tail
		| (stack, (stmnt, input, output)), LD x -> 
			let value = stmnt x in
			eval (value::stack, (stmnt, input, output)) tail
		| (z::stack, (stmnt, input, output)), ST x -> 
			let stt = Language.Expr.update x z stmnt in
			eval (stack, (stt, input, output)) tail
	)


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compileExpression expr = 
	match expr with
	| Language.Expr.Const c -> [CONST c]
	| Language.Expr.Var x -> [LD x]
	| Language.Expr.Binop (operation, leftOperation, rightOperation) -> compileExpression leftOperation @ compileExpression rightOperation @ [BINOP operation]

let rec compile statement = 
	match statement with
	| Language.Stmt.Assign (x, expr) -> compileExpression expr @ [ST x]
	| Language.Stmt.Read x -> [READ; ST x]
	| Language.Stmt.Write expr -> compileExpression expr @ [WRITE]
	| Language.Stmt.Seq (leftStatement, rightStatement) -> compile leftStatement @ compile rightStatement
