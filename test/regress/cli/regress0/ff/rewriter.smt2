; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_LRA)
; all disjuncts should be false
(declare-fun x () (_ FiniteField 5))
(assert (or
  ; direct !=
  (= #f2m5 #f1m5 )
  ; direct ==
  (not (= #f1m5 #f1m5 ))
  ; neg: all constants
  (not (= (ffneg #f1m5) #f4m5 ))
  ; add: all constants
  (not (= (ffadd #f0m5 #f1m5 #f2m5 #f3m5) #f1m5 ))
  ; add: vars cancel (w/ neg)
  (not (= (ffadd #f0m5 (ffneg x) x) #f0m5 ))
  ; add: vars cancel
  (not (= (ffadd #f0m5 (ffmul #f4m5 x) x) #f0m5 ))
  ; mul: a direct zero
  (= (ffmul #f0m5 #f1m5 #f2m5 #f3m5) #f1m5 )
  ; mul: a direct zero w/ var
  (= (ffmul #f0m5 #f1m5 x #f3m5) #f1m5 )
  ; mul: all constants
  (not (= (ffmul #f1m5 #f2m5 #f3m5) #f1m5 ))
  ; mul: a direct zero w/ var
  (not (= (ffmul x #f3m5) (ffadd x x x)))
  ; mul: a direct zero w/ monomials
  (not (= (ffmul x x #f3m5) (ffadd (ffmul x x) (ffmul #f2m5 x x))))
))
(check-sat)
