; EXPECT: sat
; Tests the ff rewriter
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
; all disjuncts should be false
(define-sort F3 () (_ FiniteField 3))
(define-sort F5 () (_ FiniteField 5))
(declare-fun a () F3)
(declare-fun b () F5)
(assert (or (= (ff.mul
    (ff.add a (as ff-0 F3))
    (ff.add a (as ff-1 F3))
    (ff.add a (as ff-2 F3))
    ) (as ff1 F3))
(= (ff.mul
    (ff.add b (as ff-0 F5))
    (ff.add b (as ff-1 F5))
    (ff.add b (as ff-2 F5))
    ) (as ff1 F5))))
(check-sat)
