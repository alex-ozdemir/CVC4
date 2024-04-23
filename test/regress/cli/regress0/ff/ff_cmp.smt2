; COMMAND-LINE: --ff-solver int
; REQUIRE: cocoa
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-option :incremental true)
(set-logic QF_FF)
(define-sort F () (_ FiniteField 17))
(declare-const x F)
(declare-const y F)
(declare-const z F)

(push)
(assert (and (ff.lt x y) (ff.lt y x))) ; UNSAT
(check-sat)
(pop)

(push)
(assert (and (ff.gt x y) (ff.gt y x))) ; UNSAT
(check-sat)
(pop)

(push)
(assert (and (ff.le x y) (ff.le y x))) ; SAT
(check-sat)
(pop)

(push)
(assert (and (ff.ge x y) (ff.ge y x))) ; SAT
(check-sat)
(pop)

(push)
(assert (and (ff.lt x y) (ff.lt y z) (ff.lt y x))) ; UNSAT
(check-sat)
(pop)

(push)
(assert (and (= (ff.mul x x) x) (ff.ge x (as ff2 F)))) ; UNSAT
(check-sat)
(pop)

(push)
(assert (and (= (ff.mul x x) x) (ff.ge x (as ff1 F)))) ; SAT
(check-sat)
(pop)
