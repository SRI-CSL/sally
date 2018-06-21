(set-logic HORN)
(set-info :status sat)

(declare-fun Inv (Int) Bool)

;; fact
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
;; chc
(assert (forall ((x Int) (y Int))
                (=> (and (Inv x) (<= x 10) (= y (+ x 1)))
                   (Inv y))))
;; query
(assert (forall ((x Int)) (=> (and (Inv x) (> x 15)) false)))

(check-sat)

