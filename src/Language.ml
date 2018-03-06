(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

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

    let elementsOperation operationsList = let binOperationList op = (ostap ($(op)), fun l r -> Binop (op, l, r))
      in List.map binOperationList operationsList;;
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (state, input, output) statement = 
      match statement with
      | Assign (var, expr) -> (Expr.update var (Expr.eval state expr) state, input, output)
      | Read (var) -> 
        (match input with
        | list::tail -> (Expr.update var list state, tail, output)
        | [] -> failwith "Empty input stream")
      | Write (expr) -> (state, input, output @ [(Expr.eval state expr)])
      | Seq (firstStatement, secondStatement) -> (eval (eval (state, input, output) firstStatement ) secondStatement)

    (* Statement parser *)
    ostap (
      parse: sequence | statement;
      statement: read | write | assign;
      read: "read" -"(" var:IDENT -")" {Read var};
      write: "write" -"(" expr:!(Expr.parse) -")" { Write expr };
      assign: var:IDENT -":=" expr:!(Expr.parse) { Assign (var, expr) };
      sequence: firstStatement:statement -";" secondStatement:parse { Seq (firstStatement, secondStatement) }
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
