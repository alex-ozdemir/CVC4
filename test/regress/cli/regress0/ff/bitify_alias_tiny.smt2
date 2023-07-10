; REQUIRES: cocoa
; EXPECT: sat
; COMMAND-LINE: --pp-ff-to-int
; COMMAND-LINE:
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
(define-sort F () (_ FiniteField 5))
(declare-fun x () F)
(declare-fun b0 () F)
(declare-fun b1 () F)
(declare-fun b2 () F)
(assert (= (ff.mul b0 b0) b0))
(assert (= (ff.mul b1 b1) b1))
(assert (= (ff.mul b2 b2) b2))
(assert
  (= x
     (ff.add
       (ff.mul (as ff1 F) b0)
       (ff.mul (as ff2 F) b1)
       (ff.mul (as ff4 F) b2)
      )))
(assert (not (and
    (= b0 (as ff1 F))
    (= b1 (as ff0 F))
    (= b2 (as ff0 F))
)))
(assert (= x (as ff1 F)))
(check-sat)
(get-model)

