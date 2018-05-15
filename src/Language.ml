(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list
    with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let rec init_list i n f = if i>=n then [] else (f i) :: (init_list (i+1) n f)
    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = init_list 0  (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

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

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )         
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
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
      | Const value -> (st, i, o, Some (Value.of_int value))
      | String str -> (st, i, o, Some (Value.of_string str))
      | Var var -> (st, i, o, Some (State.eval st var))
      | Array array -> let (st, i, o, evaluated) =
        eval_list env conf array in
        env#definition env "$array" evaluated (st, i, o, None)
      | Sexp (t, array) -> let (st, i, o, evaluated) = 
        eval_list env conf array in
        (st, i, o, Some (Value.Sexp (t, evaluated)))
      | Elem (x, pos) -> let (st, i, o, args) =
        eval_list env conf [x; pos] in
        env#definition env "$elem" args (st, i, o, None)
      | Length x -> let (st, i, o, Some arg) =
        eval env conf x in
        env#definition env "$length" [arg] (st, i, o, None)
      | Binop (op, l, r) ->
        let (_, _, _, Some arg1) as conf = eval env conf l in
        let (st, i , o, Some arg2) =  eval env conf r in
        (st, i, o, Some (Value.of_int (evalBinaryOperation op (Value.to_int arg1) (Value.to_int arg2))))
      | Call (name, args) ->
        let (st, i, o, eargs) = eval_list env conf args in 
        env#definition env name eargs (st, i, o, None)
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
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

        primary: cov:constsOrVars is:(-"[" i:parse -"]" {`Elem i} | "." %"length" {`Len})* {List.fold_left (fun x -> function `Elem i -> Elem (x, i) | `Len -> Length x) cov is};
      
        constsOrVars:
          n:DECIMAL {Const n}
        | s:STRING {String (String.sub s 1 (String.length s - 2))}
        | c:CHAR {Const (Char.code c)}
        | "[" elements:!(Util.list0)[parse] "]" {Array elements}
        | "`" t:IDENT args:(-"(" !(Util.list)[parse] -")")? {Sexp (t, match args with None -> [] | Some reallyArgs -> reallyArgs)} 
        | x:IDENT  s: ("(" args: !(Util.list0)[parse] "" {Call (x, args)} | empty {Var x}) {s}
        | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let makeSeq st_1 st_2 =
      match st_2 with
      | Skip -> st_1
      | y    -> Seq(st_1, y)

    let rec eval env ((st, i, o, r) as conf) k stmt = 
      match stmt with
      | Assign (x, is, e) -> let (st, i, o, is) = Expr.eval_list env conf is in
         let (st, i, o, Some v) = Expr.eval env (st, i, o, None) e in
         eval env (update st x v is, i, o, None) Skip k
      | Seq    (s1, s2) -> eval env conf (makeSeq s2 k) s1
      | Skip -> (match k with Skip -> conf | something -> eval env conf Skip k)
      | If (expr, thenIf, elseIf) -> let (_, _, _, Some x) as conf = Expr.eval env conf expr in if Value.to_int x <> 0 then (eval env conf k thenIf) else (eval env conf k elseIf)
      | While (expr, loopStmt) -> let (_, _, _, Some x) as conf = Expr.eval env conf expr in
        if (Value.to_int x = 0) then eval env conf Skip k else eval env conf (makeSeq stmt k) loopStmt
      | Repeat (loopStmt, expr) ->  eval env conf (makeSeq (While (Expr.Binop ("==", expr, Expr.Const 0), loopStmt)) k) loopStmt
      | Call (f, args) -> eval env (Expr.eval env conf (Expr.Call (f, args))) k Skip
      | Return res -> match res with
      | None -> (st, i, o, None)
      | Some resExpr -> Expr.eval env conf resExpr


    let rec parse_elif elifArg elseArg =  match elifArg with
    | [] -> elseArg
    | (condition, action)::tail -> If (condition, action, parse_elif tail elseArg)

    let parse_else elifArg elseArg = 
      let parsed = match elseArg with
      | None -> Skip
      | Some action -> action
    in parse_elif elifArg parsed  
         
    (* Statement parser *)
    ostap (parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;
      
      stmt:
      x:IDENT 
        assign_call: (
          index:(-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse)    {Assign (x, index, e)}
          | "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)}
        ) {assign_call}
      | %"skip"                         {Skip}
      | %"if" condition: !(Expr.parse) %"then" action:parse 
        elifArg:(%"elif" !(Expr.parse) %"then" parse)*
        elseArg:(%"else" parse)?
        %"fi"                                              { If (condition, action, parse_else elifArg elseArg)}
      | %"while" condition: !(Expr.parse) %"do" action:parse %"od"  { While (condition, action) }
      | %"repeat" action:parse %"until" condition: !(Expr.parse)    { Repeat (action, condition) }
      | %"return" e:!(Expr.parse)? {Return e}
      | %"for" initialize:parse "," condition: !(Expr.parse)
        "," increment:parse %"do" action:parse %"od"             { Seq (initialize, While (condition, Seq (action, increment))) }
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
