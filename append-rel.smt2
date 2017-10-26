
; expect: SAT

(declare-datatypes () ((U (U1) (U2))))

(declare-datatypes
   ()
   ((list (cons (hd U) (tail list)) 
          (nil))))

(declare-rel len (list Int))
(declare-rel append (list list list))

(declare-var l1 list)
(declare-var l2 list)
(declare-var l3 list)
(declare-var l4 list)
(declare-var x U)
(declare-var n Int)
(declare-var n2 Int)

(rule (len nil 0))
(rule (=> (and (len l1 n)
               (= (+ 1 n) n2))
          (len (cons x l1) n2)))

(rule (=> (= l1 l2) (append nil l1 l2)))
(rule (=> (append l1 l2 l3) (append (cons x l1) l2 (cons x l3))))

; queries

(declare-rel q1 (list))
(rule (=> (append (cons U1 nil) (cons U2 nil) l1)
          (q1 l1)))

(query q1 :print-certificate true)

; should be sat, with l1=[U1], l2=[U2]
(declare-rel q2 (list list))
(rule (=> (and (len l1 1) (len l2 1) (not (= l1 l2)))
          (q2 l1 l2)))

(query q2 :print-certificate true)

(declare-rel q_final (list list))
(rule (=> (and (append l1 l2 l3)
               (append l2 l1 l4)
               (len l1 1)
               (len l2 1)
               (not (= l3 l4))
               )
          (q_final l1 l2)))

(query q_final :print-certificate true)

