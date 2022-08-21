open Printf

(* Définitions de terme, test et programme *)
type term = 
 | Const of int
 | Var of int
 | Add of term * term
 | Mult of term * term

type test = 
 | Equals of term * term
 | LessThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)
 
type program = {nvars : int; 
                inits : term list; 
                mods : term list; 
                loopcond : test; 
                assertion : test}

let x (n: int): string = "x" ^ (string_of_int n)

(* Question 1. Écrire des fonctions `str_of_term` et `str_of_test` qui
   convertissent des termes et des tests en chaînes de caractères du
   format SMTLIB.

  Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)".  *)
let rec str_of_term (t: term): string =
  match t with
  | Const (integer) -> string_of_int integer
  | Var (n) -> x n
  | Add (term1, term2) -> "(+ " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"
  | Mult (term1, term2) -> "(* " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"

let str_of_test (t: test): string =
  match t with
  | Equals (term1, term2) -> "(= " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"
  | LessThan (term1, term2) -> "(< " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"

(* Question 2. Écrire une fonction str_condition qui prend une liste
   de termes t1, ..., tk et retourne une chaîne de caractères qui
   exprime que le tuple (t1, ..., tk) est dans l'invariant.  Par
   exemple, str_condition [Var 1; Const 10] retourne "(Invar x1 10)".
   *)
let str_condition (terms: term list): string =

  let rec str_condition_rec (terms: term list) (acc: string): string =
    match terms with
    | [] -> acc ^ ")"
    | term::terms' -> str_condition_rec terms' (acc ^ " " ^ (str_of_term term)) in

  str_condition_rec terms "(Invar"

(* Question 3. Écrire une fonction str_assert_for_all qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMTLIB qui correspond à la formule "forall x1 ... xk
   (s)".

  Par exemple, str_assert_forall 2 "< x1 x2" retourne : "(assert
   (forall ((x1 Int) (x2 Int)) (< x1 x2))".  *)
let str_assert (str: string): string = "(assert " ^ str ^ ")"

let str_assert_forall (n: int) (str: string): string =
  let rec str_of_vars (i: int) (acc: string): string =
    match i with
    | 0 -> acc ^ ")"
    | _ -> str_of_vars (i - 1) (acc ^ (if String.equal acc "(" then "" else " ") ^ "(" ^ (x (n - i + 1)) ^ " Int)") in

    str_assert ("(forall " ^ (str_of_vars n "(") ^ " (" ^ str ^ "))")

let string_repeat (str: string) (n: int): string =
  Array.fold_left (^) "" (Array.make n str)

let terms_of_nvars (n: int): term list =

  let rec terms_of_nvars_rec (i: int) (acc: term list): term list =
    match i with
    | 0 -> acc
    | _ -> terms_of_nvars_rec (i - 1) (acc @ [Var (n - i + 1)]) in
  
  terms_of_nvars_rec n []

let str_of_test_inverted (t: test): string =
  match t with
  | Equals (term1, term2) -> "(not (= " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ "))"
  | LessThan (term1, term2) -> "(>= " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"

(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)
let smtlib_of_wa p =

  let declare_invariant n =
      "; Synthèse d'invariant de programme.\n"
    ^ "; Déclaration d'un symbole de relation non interprété 'Invar'.\n"
    ^ "(declare-fun Invar (Int" ^ string_repeat " Int" (n - 1) ^  ") Bool)" in
  let initial_condition p =
      "; Invar contient la configuration initiale.\n"
    ^ str_assert (str_condition p.inits) in
  let loop_condition p =
      "; Invar doit être un invariant de boucle.\n"
      ^ str_assert_forall p.nvars ("=> " ^
          "(and "
        ^ (str_condition (terms_of_nvars p.nvars) ^ " "
        ^ (str_of_test p.loopcond))
        ^ ") "
      ^ (str_condition p.mods)) in
  let assertion_condition p =
      "; Invar doit être sûr.\n"
    ^ str_assert_forall p.nvars ("=> " ^
        "(and "
      ^ (str_condition (terms_of_nvars p.nvars) ^ " "
      ^ (str_of_test_inverted p.loopcond))
      ^ ") "
    ^ (str_of_test p.assertion)) in
  let call_solver =
      "; Appel au solveur.\n"
    ^ "(check-sat-using (then qe smt))\n"
    ^ "(get-model)\n"
    ^ "(exit)\n" in

  String.concat "\n" [
    declare_invariant p.nvars;
    initial_condition p;
    loop_condition p;
    assertion_condition p;
    call_solver
  ]

(*
int i = 0;
int v = 0;
while (i < 3) {
    v = v + 3;
    i = i + 1;
}
assert (v == 9);
*)
let p1 = {
  nvars = 2;
  inits = [(Const 0); (Const 0)];
  loopcond = LessThan ((Var 1), (Const 3));
  mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 3))];
  assertion = Equals ((Var 2), (Const 9))
}

let () = Printf.printf "; p1\n%s" (smtlib_of_wa p1)

(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMTLIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. Ajoutez dans la variable p2 ci-dessous au moins
   un autre programme test, et vérifiez qu'il donne un fichier SMTLIB
   de la forme attendue. *)

(*
int i = 0;
int j = 1;
int k = 5;
while (i < 10) {
	i = i + 2;
	j = j + 1;
	k = k + j;
}
assert (j < k);
*)
let p2 = {
  nvars = 3;
  inits = [(Const 0) ; (Const 1); (Const 5)];
  loopcond = LessThan ((Var 1), (Const 10));
  mods = [Add ((Var 1), (Const 2)); Add ((Var 2), (Const 1)); Add ((Var 3), (Var 2))];
  assertion = LessThan ((Var 2), (Var 3))
}

let () = Printf.printf "\n; p2\n%s" (smtlib_of_wa p2)