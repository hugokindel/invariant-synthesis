; Synthèse d'invariant de programme.
; Déclaration d'un symbole de relation non interprété 'Invar'.
(declare-fun Invar (Int Int) Bool)
; Invar contient la configuration initiale.
(assert (Invar 0 0))
; Invar doit être un invariant de boucle.
(assert (forall ((i Int) (v Int)) (=> (and (Invar i v) (< i 3)) (Invar (+ i 1) (+ v 3)))))
; Invar doit être sûr.
(assert (forall ((i Int) (v Int)) (=> (and (Invar i v) (>= i 3)) (= v 9))))
; Appel au solveur.
(check-sat-using (then qe smt))
(get-model)
(exit)