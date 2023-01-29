open Test_simple ;;
open Expr ;;
open Evaluation ;;
open Env ;;

let letrec_exp = 
  Letrec ("f", Fun ("x", Conditional (
                           Binop (Equals, Var("x"), Num(0)), Num(1),
                           Binop (Times, Var("x"), 
                                         App (Var ("f"), 
                                              Binop (Minus, Var("x"), 
                                                            Num(1)))))),
                           App(Var("f"), Num(4))) ;;
let let_exp = Let ("x", Num 5, Binop (Plus, Var "y", Num 5)) ;;
let fun_exp = Fun ("x", Binop (Plus, Var "y", Num 5)) ;;
let app_exp = App (Fun ("x", Binop (Plus, Var "x", Num 5)), Num 3) ;;
let conditional_exp = Conditional (Bool true, 
                                   Binop (Plus, Var "x", Var "y"), 
                                   Var "y") ;;
let free_vars_test () =
  unit_test (free_vars (Num 3) = vars_of_list []) "free_vars Num";
  unit_test (free_vars (Bool true) = vars_of_list []) "free_vars Bool";
  unit_test (free_vars (Raise) = vars_of_list []) "free_vars Raise";
  unit_test (free_vars (Unassigned) = vars_of_list []) "free_vars Unassigned";
  unit_test (free_vars (Var "x") = vars_of_list ["x"]) "free_vars Var";
  unit_test (free_vars (Unop (Negate, Binop (Plus, Var "x", Var "y"))) = 
            vars_of_list ["x"; "y"]) "free_vars Unop";
  unit_test (free_vars (Binop (Plus, Var "x", Var "y")) = 
            vars_of_list ["x"; "y"]) "free_vars Binop";
  unit_test (free_vars (conditional_exp) = vars_of_list ["x"; "y"]) 
            "free_vars Conditional";
  unit_test (free_vars (app_exp) = vars_of_list []) "free_vars App";
  unit_test (free_vars (fun_exp) = vars_of_list ["y"]) "free_vars Fun";
  unit_test (free_vars (let_exp) = vars_of_list ["y"]) "free_vars Let";
  unit_test (free_vars (letrec_exp) = vars_of_list []) "free_vars Letrec" ;;

let subst_test () =
  unit_test (subst "x" (Num 5) (Var "x") = Num 5) "subst Var";
  unit_test (subst "x" (Num 6) (Num 5) = Num 5) "subst Num";
  unit_test (subst "x" (Num 7) (Bool true) = Bool true) "subst Bool";
  unit_test (subst "x" (Num 8) Raise = Raise) "subst Raise";
  unit_test (subst "x" (Num 9) Unassigned = Unassigned) "subst Unassigned";
  unit_test (subst "x" (Num 10) 
                       (Unop (Negate, Binop (Plus, Var "x", Var "y"))) =
            Unop (Negate, Binop (Plus, Num 10, Var "y"))) "subst Unop";
  unit_test (subst "x" (Num 9) (Binop (Plus, Var "x", Var "y")) = 
            Binop (Plus, Num 9, Var "y")) "subst Binop";
  unit_test (subst "x" (Num 8) (conditional_exp) = 
            Conditional (Bool true, Binop (Plus, Num 8, Var "y"), Var "y"))
            "subst Conditional";
  unit_test (subst "x" (Num 7) (app_exp) = 
            App (Fun ("x", Binop (Plus, Var "x", Num 5)), Num 3)) "subst App";
  unit_test (subst "x" (Num 6) (fun_exp) = 
            Fun ("x", Binop (Plus, Var "y", Num 5))) "subst Fun";
  unit_test (subst "x" (Num 5) (let_exp) = 
            Let ("x", Num 5, Binop (Plus, Var "y", Num 5))) "subst Let";
  unit_test (exp_to_concrete_string (subst "x" (Num 4) letrec_exp) =
            "let rec f = fun x -> if x = 0 then 1 " ^ 
            "else x * (f) (x - 1) in (f) (4)")
            "subst Letrec" ;;

let empty_env = Env.empty ;;
let existing_env = Env.extend (empty_env ()) "x" (ref (Env.Val (Num 3))) ;;
let updated_env = Env.extend existing_env "y" (ref (Env.Val (Bool true))) ;;

let extend_test () =
  unit_test (Env.env_to_string (empty_env ()) = "}") "empty environment";
  unit_test (Env.env_to_string existing_env = "{x -> (3)}") 
            "extend to empty environment";
  unit_test (Env.env_to_string updated_env = "{y -> (true), {x -> (3)}") 
            "extend to existing environment" ;;

let close_test () =
  unit_test (Env.close letrec_exp (empty_env ()) = 
             Closure (letrec_exp, empty_env ())) "close empty environment";
  unit_test (Env.close app_exp existing_env = Closure (app_exp, existing_env)) 
            "close existing environment";
  unit_test (Env.close fun_exp updated_env = Closure (fun_exp, updated_env)) 
            "close complex existing environment" ;;

let lookup_test () =
  unit_test (Env.lookup existing_env "x" = Env.Val (Num 3)) 
            "lookup exists in environment";
  unit_test (Env.lookup updated_env "y" = Env.Val (Bool true)) 
            "lookup exists in complex environment";
  unit_test (Env.lookup updated_env "x" = Env.Val (Num 3)) 
            "lookup other variable in complex environment" ;;

let concrete_of_val (v : Env.value) : string = 
  exp_to_concrete_string (exp_of_val v) ;;

let eval_s_test () = 
  unit_test (concrete_of_val (eval_s (Num 1) (empty_env ())) = "1") 
            "eval_s Num";
  unit_test (concrete_of_val (eval_s (Bool true) (empty_env ())) = "true") 
            "eval_s Bool";
  unit_test (concrete_of_val (eval_s (Unop (Negate, 
                                            Binop (Plus, Num 2, Num 8)))
                                     (empty_env ())) = "-10") 
            "eval_s Unop";
  unit_test (concrete_of_val (eval_s (Binop (Plus, Num 2, Num 8)) 
                                     (empty_env ())) = "10") 
            "eval_s Binop";
  unit_test (concrete_of_val (eval_s (Conditional (Bool true, Num 1, Num 2)) 
                                     (empty_env ())) = "1")
            "eval_s Conditional";
  unit_test (concrete_of_val (eval_s app_exp (empty_env ())) = "8") 
            "eval_s App";
  unit_test (concrete_of_val (eval_s fun_exp (empty_env ())) = 
             exp_to_concrete_string fun_exp) "eval_s Fun";
  unit_test (concrete_of_val (eval_s (Let ("x", Num 5, 
                                                Binop (Plus, Var "x", Num 5)))
                                     (empty_env ())) = "10") 
            "eval_s Let";
  unit_test (concrete_of_val (eval_s letrec_exp (empty_env ())) = "24") 
            "eval_s Letrec" ;;

let eval_d_test () = 
  unit_test (concrete_of_val (eval_d (Var "x") existing_env) = "3") 
            "eval_d Var";
  unit_test (concrete_of_val (eval_d (Num 1) (empty_env ())) = "1") 
            "eval_d Num";
  unit_test (concrete_of_val (eval_d (Bool true) (empty_env ())) = "true") 
            "eval_d Bool";
  unit_test (concrete_of_val (eval_d (Unop (Negate, 
                                            Binop (Plus, Num 2, Num 8)))
                                      (empty_env ())) = "-10") 
            "eval_d Unop";
  unit_test (concrete_of_val (eval_d (Binop (Plus, Num 2, Num 8)) 
                                      (empty_env ())) = "10") 
            "eval_d Binop";
  unit_test (concrete_of_val (eval_d (Conditional (Bool true, Num 1, Num 2)) 
                                      (empty_env ())) = "1")
            "eval_d Conditional";
  unit_test (concrete_of_val (eval_d app_exp (empty_env ())) = "8") 
            "eval_d App";
  unit_test (concrete_of_val (eval_d fun_exp (empty_env ())) = 
              exp_to_concrete_string fun_exp) "eval_d Fun";
  unit_test (concrete_of_val (eval_d (Let ("x", Num 5, 
                                                Binop (Plus, Var "x", Num 5)))
                                      (empty_env ())) = "10") 
            "eval_d Let";
  unit_test (concrete_of_val (eval_d letrec_exp (empty_env ())) = "24") 
            "eval_d Letrec" ;;

let eval_l_test () = 
  unit_test (concrete_of_val (eval_l (Var "x") existing_env) = "3") 
            "eval_l Var";
  unit_test (concrete_of_val (eval_l (Num 1) (empty_env ())) = "1") 
            "eval_l Num";
  unit_test (concrete_of_val (eval_l (Bool true) (empty_env ())) = "true") 
            "eval_l Bool";
  unit_test (concrete_of_val (eval_l (Unop (Negate, 
                                            Binop (Plus, Num 2, Num 8)))
                                      (empty_env ())) = "-10") 
            "eval_l Unop";
  unit_test (concrete_of_val (eval_l (Binop (Plus, Num 2, Num 8)) 
                                      (empty_env ())) = "10") 
            "eval_l Binop";
  unit_test (concrete_of_val (eval_l (Conditional (Bool true, Num 1, Num 2)) 
                                      (empty_env ())) = "1")
            "eval_l Conditional";
  unit_test (concrete_of_val (eval_l app_exp (empty_env ())) = "8") 
            "eval_l App";
  unit_test (concrete_of_val (eval_l fun_exp (empty_env ())) = 
              exp_to_concrete_string fun_exp) "eval_l Fun";
  unit_test (concrete_of_val (eval_l (Let ("x", Num 5, 
                                                Binop (Plus, Var "x", Num 5)))
                                      (empty_env ())) = "10") 
            "eval_l Let";
  unit_test (concrete_of_val (eval_l letrec_exp (empty_env ())) = "24") 
            "eval_l Letrec" ;;

let run_tests () =
  free_vars_test (); 
  subst_test ();
  extend_test ();
  close_test ();
  lookup_test ();
  eval_s_test ();
  eval_d_test ();
  eval_l_test () ;;

let _ = run_tests () ;;
