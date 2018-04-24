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
    
    let rec eval env ((st, i, o, r) as conf) expr = 
      match expr with
      | Const value -> (st, i, o, Some value)
      | Var var -> (st, i, o, Some (State.eval st var))
      | Binop (op, l, r) ->
        let (st', i', o', Some left) = eval env conf l in
        let (st'', i'', o'', Some right) = eval env (st', i', o', Some left) r in
        (st'', i'', o'', Some (evalBinaryOperation op left right))
      | Call (name, args) ->
        let rec evaluateArgs env conf args =
          match args with
          | expr::args' ->
            let (st', i', o', Some evaluated_args) as conf' = eval env conf expr in
            let evaluated_args', conf' = evaluateArgs env conf' args' in
              evaluated_args::evaluated_args', conf'
          | [] -> [], conf
        in let evaluated_args, conf' = evaluateArgs env conf args in
        env#definition env name evaluated_args conf 
         
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt =
      let makeSeq st_1 st_2 =
    		(match st_2 with
        | Skip -> st_1
			  | _    -> Seq(st_1, st_2)) in
		  match stmt with 
			| Assign (var, expr) ->
        let (st, i,o, Some v) = Expr.eval env conf expr in
        eval env (State.update var v st, i, o, r) 
        Skip k
			| Read var -> eval env (State.update var (List.hd i) st, List.tl i, o, r) 
        Skip k
			| Write expr ->
			  let (st, i, o, Some v) = Expr.eval env conf expr in
			  eval env (st, i, o @ [v], r) 
        Skip k
			| Seq (st1, st2) -> eval env conf (makeSeq st2 k) st1
      | Skip ->
        match k with
        | Skip -> conf
        | _    -> eval env conf 
        Skip k 
			| If (cond, l, r) ->
			  let (_, _, _, Some v) = Expr.eval env conf cond in
			  eval env conf k (if v <> 0 then l else r) 
			| While (cond, st) -> 
        eval env conf k 
          (If (cond, Seq (st, While (cond, st)), Skip))
			| Repeat (st, cond) -> 
        eval env conf k 
          (Seq (st, If (cond, Skip, Repeat (st, cond))))
			| Return expr -> (
				match expr with
				| None -> conf
				| Some expr -> Expr.eval env conf expr
        )
			| Call (func, args) -> 
        eval env (Expr.eval env conf (Expr.Call (func, args))) 
        Skip k
         
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
      repeat_ : "repeat" stmt:parse "until" expr:!(Expr.parse) {Repeat (stmt, expr)};
      skip: "skip" {Skip};
      call: var:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (var, args)};
      sequence: firstStatement:statement -";" secondStatement:parse { Seq (firstStatement, secondStatement) }
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
