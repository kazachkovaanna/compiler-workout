(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let fail = failwith "Undefined var"
    let empty = { g = fail; l = fail; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = 
      let update' x v s = fun y-> if x = y then v else s y in
        if List.mem x s.scope
          then {s with l = update' x v s.l}
          else {s with g = update' x v s.g}
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if List.mem x s.scope then (s.l x) else (s.g x)

    (* Creates a new scope, based on a given state *)
    let enter st xs = {st with g = st.g; scope = xs;}

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let evalBinaryOperation operation exprLeft exprRight =
      let booleanOfInt value = if value = 0 then false else true in
      let intOfBoolean value = if value = true then 1 else 0 in
      match operation with
      | "+" -> exprLeft + exprRight
      | "-" -> exprLeft - exprRight
      | "*" -> exprLeft * exprRight
      | "/" -> exprLeft / exprRight
      | "%" -> exprLeft mod exprRight
      | "==" -> intOfBoolean(exprLeft == exprRight)
      | "!=" -> intOfBoolean(exprLeft != exprRight)
      | "<"  -> intOfBoolean(exprLeft < exprRight)
      | "<=" -> intOfBoolean(exprLeft <= exprRight)
      | ">"  -> intOfBoolean(exprLeft > exprRight)
      | ">=" -> intOfBoolean(exprLeft >= exprRight)
      | "&&" -> intOfBoolean(booleanOfInt exprLeft && booleanOfInt exprRight)
      | "!!" -> intOfBoolean(booleanOfInt exprLeft || booleanOfInt exprRight)
      | _ -> failwith "Wrong operation"
    
    let rec eval state expr =
      let eval' = eval state in
      match expr with
      | Const value -> value
      | Var var -> state var
      | Binop(op, l, r) -> evalBinaryOperation op (eval' l) (eval' r)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)

    let elementsOperation operationsList = let binOperationList op = (ostap ($(op)), fun l r -> Binop (op, l, r))
      in List.map binOperationList operationsList;;

    ostap (
      parse:
        !(Ostap.Util.expr
          (fun x -> x)
          [|
            `Lefta, elementsOperation ["!!"];
            `Lefta, elementsOperation ["&&"];
            `Nona,  elementsOperation [">="; ">"; "<="; "<"; "=="; "!="];
            `Lefta, elementsOperation ["+"; "-"];
            `Lefta, elementsOperation ["*"; "/"; "%"]
          |]
          primary
        );
      primary: 
        var:IDENT {Var var} 
        | literal:DECIMAL {Const literal} 
        | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec zip = function
      | x::xs, y::ys -> (x, y) :: (zip (xs, ys))
      | [], [] -> []
      | _, _ -> failwith "Not even number"

    let rec eval env ((state, input, output) as conf) statement = 
      match statement with
      | Assign (var, expr) -> (State.update var (Expr.eval state expr) state, input, output)
      | Read (var) -> 
        (match input with
        | list::tail -> (State.update var list state, tail, output)
        | [] -> failwith "Empty input stream")
      | Write (expr) -> (state, input, output @ [(Expr.eval state expr)])
      | Seq (firstStatement, secondStatement) -> (eval (eval (state, input, output) firstStatement ) secondStatement)
      | Skip -> (state, input, output)
      | If (expr, firstStatement, secondStatement) -> if Expr.eval state expr != 0 
        then
          eval (state, input, output) firstStatement 
        else 
          eval (state, input, output) secondStatement
      | While (expr, stmt) -> if Expr.eval state expr !=0 
        then
          eval (eval (state, input, output) stmt) statement
        else 
          (state, input, output)
      | Repeat (expr, stmt) -> 
        let (state', input', output') = eval (state, input, output) stmt in
          if Expr.eval state' expr == 0 
            then 
              eval(state', input', output') statement
            else
              (state', input', output')
      |Call (funcName, args) ->
        let params, fvars, body = env#definition funcName in
        let evaluatedArgs = List.map (Expr.eval st) args in
        let assign st (variable, value) = State.update variable value st in
        let startState = State.enter st (params @ fvars) in
        let localState = List.fold_left assign startState(zip(params, evaluatedArgs)) in
        let endState, newInput, newOutput = eval env (localState, input, output) body in
        (State.leave endState st, newInput, newOutput)
      | _ -> failwith "Error: not a statement" 
                                
    (* Statement parser *)
    ostap (
      parse: sequence | statement;
      statement: read | write | assign | if_ | while_ | for_ | repeat_ | skip | call;
      read: "read" -"(" var:IDENT -")" {Read var};
      write: "write" -"(" expr:!(Expr.parse) -")" { Write expr };
      assign: var:IDENT -":=" expr:!(Expr.parse) { Assign (var, expr) };
      if_: "if" expr:!(Expr.parse) "then" stmt:parse "fi" {If (expr, stmt, Skip)}
         | "if" expr:!(Expr.parse) "then" stmt1:parse  else_elif:else_or_elif "fi" {If (expr, stmt1, else_elif)};
      else_or_elif : else_ | elif_;
      else_: "else" stmt:parse {stmt};
      elif_: "elif" expr:!(Expr.parse) "then" stmt1:parse stmt2:else_or_elif "fi" {If (expr, stmt1, stmt2)};
      while_: "while" expr:!(Expr.parse) "do" stmt:parse "od" {While (expr, stmt)};
      for_: "for" initial:parse "," expr:!(Expr.parse) "," stmt1:parse "do" stmt2:parse "od" {Seq (initial, While(expr, Seq(stmt1, stmt2)))};
      repeat_ : "repeat" stmt:parse "until" expr:!(Expr.parse) {Repeat (expr, stmt)};
      skip: "skip" {Skip};
      sequence: firstStatement:statement -";" secondStatement:parse { Seq (firstStatement, secondStatement) };
      call: var:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (var, args)}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: %"fun" funcName:IDENT "(" args:(names | none) ")" vars:(-(%"local") names | none)
        "{" body:!(Stmt.parse) "}" { funcName, (args, vars, body) } ;
      none : empty{ [] };
      names: head:IDENT tail:((-"," IDENT)* ) {head :: tail}
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
  let module Module = Map.Make (String) in
  let defsMap = List.fold_left (fun map (f, data) -> Module.add f data map) Module.empty defs in
  let env = (object method defenition f = Module.find f defsMap end) in
  let _, _, output = Stmt.eval env (State.empty, i, []) body in 
  output

                                   
(* Top-level parser *)
ostap (
  defs: !(Definition.parse) * ;
  parse: defs:defs body:!(Stmt.parse) {defs, body}
)
