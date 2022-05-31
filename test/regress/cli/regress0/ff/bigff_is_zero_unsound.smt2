; EXPECT: sat
; x, m, is_zero: field
; The constraints mx - 1 + is_zero = 0
;                 is_zero*m = 0                     ;; Note: this *should* be is_zero*x=0
; Imply that is_zero is zero or one and = (x == 0)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
(define-sort F () (_ FiniteField 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787))
(declare-fun x () F)
(declare-fun m () F)
(declare-fun is_zero () F)
(assert (not (=>
  (and (= (as ff0 F)
          (ffadd (ffmul m x) (as ff-1 F) is_zero))
       (= (as ff0 F) (ffmul is_zero m)))
  (and (or (= (as ff0 F) is_zero) (= (as ff1 F) is_zero))
       (= (= (as ff1 F) is_zero) (= x (as ff0 F))))
)))
(check-sat)
