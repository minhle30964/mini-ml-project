(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids) and sets of them
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)

let rec free_vars (exp : expr) : varidset =
  let union (e1 : expr) (e2 : expr) : varidset = 
    SS.union (free_vars e1) (free_vars e2) in
  match exp with
  | Num _ 
  | Bool _ 
  | Raise 
  | Unassigned -> SS.empty
  | Var (v) -> SS.add v SS.empty 
  | Unop (_, e) -> free_vars e
  | App (exp_P, exp_Q)
  | Binop (_, exp_P, exp_Q) -> union exp_P exp_Q
  | Conditional (e1, e2, e3) -> SS.union (union e1 e2) (free_vars e3)
  | Fun (v, exp_P) -> SS.remove v (free_vars exp_P) 
  | Let (v, exp_P, exp_Q) -> SS.union (SS.remove v (free_vars exp_Q)) 
                                      (free_vars exp_P)
  | Letrec (v, exp_P, exp_Q) -> SS.remove v (union exp_Q exp_P) ;;
  
(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no variable names use the
   prefix "var". (Otherwise, they might accidentally be the same as a
   generated variable name.) *)
let new_varname () : varid =
  let gensym : string -> string =
    let suffix = ref 0 in
    fun str -> let symbol = str ^ string_of_int !suffix in
               suffix := !suffix + 1;
               symbol in
  gensym "var" ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  match exp with
  | Var (var) -> if var = var_name then repl
                 else exp
  | Num _ | Bool _ | Raise | Unassigned -> exp
  | Unop (_, exp_Q) -> Unop (Negate, subst var_name repl exp_Q)
  | Binop (b, exp_Q, exp_R) -> Binop (b, subst var_name repl exp_Q, 
                                         subst var_name repl exp_R)
  | Conditional (e1, e2, e3) -> Conditional (subst var_name repl e1, 
                                             subst var_name repl e2, 
                                             subst var_name repl e3)
  | Fun (v, exp_Q) -> if v = var_name then Fun (v, exp_Q)
                      else 
                        if not (SS.mem v (free_vars repl)) 
                        then Fun (v, subst var_name repl exp_Q)
                        else let z = new_varname () in 
                             Fun (z, subst var_name repl 
                                    (subst v (Var z) exp_Q))
  | Let (v, exp_Q, exp_R) -> 
      if v = var_name 
      then Let (v, subst var_name repl exp_Q, exp_R)
      else 
        if not (SS.mem v (free_vars repl)) 
        then Let (v, subst var_name repl exp_Q, 
                     subst var_name repl exp_R)
        else let z = new_varname () in 
             Let (z, subst var_name repl exp_Q, 
                     subst var_name repl 
                          (subst v (Var z) exp_R)) 
  | Letrec (v, exp_Q, exp_R) -> 
      if v = var_name 
      then Letrec (v, exp_Q, exp_R)
      else 
        if not (SS.mem v (free_vars repl)) 
        then Letrec (v, subst var_name repl exp_Q, 
                      subst var_name repl exp_R)
        else let z = new_varname () in 
              Letrec (z, subst var_name repl (subst v (Var z) exp_Q), 
                         subst var_name repl 
                              (subst v (Var z) exp_R))
  | App (exp_Q, exp_R) -> App (subst var_name repl exp_Q, 
                               subst var_name repl exp_R) ;;
     
(*......................................................................
  String representations of expressions
 *)
   
(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
let rec exp_to_concrete_string (exp : expr) : string =
  let binop_to_string (b : binop) : string = 
    match b with
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Equals -> "="
    | LessThan -> "<" in
  match exp with 
  | Var (var_name) -> var_name 
  | Num (n) -> string_of_int n 
  | Bool (b) -> string_of_bool b 
  | Unop (_, e) -> "-" ^ exp_to_concrete_string e
  | Binop (b, e1, e2) -> (exp_to_concrete_string e1) ^ " " ^
                         (binop_to_string b) ^ " " ^
                         (exp_to_concrete_string e2)
  | Conditional (e1, e2, e3) -> "if " ^ exp_to_concrete_string e1 ^ 
                                " then " ^ exp_to_concrete_string e2 ^ 
                                " else " ^ exp_to_concrete_string e3
  | Fun (v, e) -> "fun " ^ v ^ " -> " ^ exp_to_concrete_string e
  | Let (v, e1, e2) -> "let " ^ v ^ " = " ^ exp_to_concrete_string e1 ^ 
                       " in " ^ exp_to_concrete_string e2
  | Letrec (v, e1, e2) -> "let rec " ^ v ^ " = " ^ exp_to_concrete_string e1 ^
                          " in " ^ exp_to_concrete_string e2 
  | Raise -> "raise" 
  | Unassigned -> "unassigned"
  | App (e1, e2) -> "(" ^ exp_to_concrete_string e1 ^ ") " ^
                    "(" ^ exp_to_concrete_string e2 ^ ")" ;;
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  let binop_to_string (b : binop) : string = 
    match b with
    | Plus -> "Plus"
    | Minus -> "Minus"
    | Times -> "Times"
    | Equals -> "Equals"
    | LessThan -> "LessThan" in
  match exp with
  | Var (v) -> "Var(" ^ v ^ ")"
  | Num (n) -> "Num(" ^ string_of_int n ^ ")"
  | Bool (b) -> "Bool(" ^ string_of_bool b ^ ")"
  | Unop (_, e) -> "Unop(Negate, " ^ exp_to_abstract_string e ^ ")"
  | Binop (op, e1, e2) -> "Binop(" ^ binop_to_string op ^ ", " ^ 
                                     exp_to_abstract_string e1 ^ ", " ^ 
                                     exp_to_abstract_string e2 ^ ")"
  | Conditional (e1, e2, e3) -> "Conditional(" ^ 
                                exp_to_abstract_string e1 ^ ", " ^ 
                                exp_to_abstract_string e2 ^ ", " ^
                                exp_to_abstract_string e3 ^ ")"
  | Fun (v, e) -> "Fun(" ^ v ^ ", " ^ exp_to_abstract_string e ^ ")"
  | Let (v, e1, e2) -> "Let(" ^ v ^ ", " ^ 
                       exp_to_abstract_string e1 ^ ", " ^
                       exp_to_abstract_string e2 ^ ")"
  | Letrec (v, e1, e2) -> "Letrec(" ^ v ^ ", " ^ 
                          exp_to_abstract_string e1 ^ ", " ^
                          exp_to_abstract_string e2 ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (e1, e2) -> "App(" ^ exp_to_abstract_string e1 ^ ", " ^
                             exp_to_abstract_string e2 ^ ")" ;;
