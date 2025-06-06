; REQUIRES: glpk
; COMMAND-LINE: --use-approx
; DISABLE-TESTER: cpc
;; Overloading of functions not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic UFNIA)
(set-info :source "Reduced from regression 'bug812.smt2' using ddSMT to exercise GLPK")
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun s (Int Int) Int)
(declare-fun P (Int Int Int) Int)
(declare-fun p (Int) Int)
(declare-fun H (Int Int) Int)
(declare-fun H (Int Int Int) Int)
(declare-fun R (Int Int) Int)
(assert (and (forall ((? Int)) (! (= (R ? 0) (s 0 0)) :pattern ((P 0 ? 0)))) (forall ((x Int)) (! false :pattern ((s x (s 0 0)) (s x (H 0 0))))) (forall ((? Int)) (! (exists ((k Int)) (= (* ? k) (- 1 (s 0 0)))) :pattern ((R ? 0)))) (forall ((x Int) (? Int) (z Int)) (! (= 0 (s (H 0 0) (P 0 ? (H 0 0)))) :pattern ((H x ? z))))))
(assert (= 0 (H (s 0 0) 2 (p 0))))
(check-sat)
