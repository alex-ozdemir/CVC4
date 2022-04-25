; EXPECT: unsat
; Tests the ff rewriter
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_LRA)
; all disjuncts should be false
(declare-fun x () (_ FiniteField 5))
(assert (= (ffmul x x) x))
; (assert (= (ffmul (ffadd x #f2m5) (ffadd x #f2m5)) (ffadd x #f2m5)))
(assert (= x #f2m5))
(check-sat)
