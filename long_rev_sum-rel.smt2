
; sat

(declare-datatypes () ((nat (s (select_s_0 nat)) 
                            (z))))

(declare-datatypes
   ()
   ((list (cons (hd nat) (tail list))
          (nil))))

(declare-var $x nat)
(declare-var $y nat)
(declare-var $z nat)
(declare-var $n Int)
(declare-var $n2 Int)
(declare-var $l1 list)
(declare-var $l2 list)
(declare-var $l3 list)

; plus
(declare-rel plus (nat nat nat))

(rule (plus z $x $x))
(rule (=> (plus $x $y $z) (plus (s $x) $y (s $z))))

; sum
(declare-rel sum (list nat))

(rule (sum nil z))
(rule (=> (and (sum $l1 $y) (plus $x $y $z))
          (sum (cons $x $l1) $z)))

; length
(declare-rel len (list Int))

(rule (len nil 0))
(rule (=> (and (len $l1 $n)
               (= (+ 1 $n) $n2))
          (len (cons $x $l1) $n2)))

; append
(declare-rel append (list list list))

(rule (=> (= $l1 $l2) (append nil $l1 $l2)))
(rule (=> (append $l1 $l2 $l3) (append (cons $x $l1) $l2 (cons $x $l3))))

; rev
(declare-rel rev (list list))

(rule (rev nil nil))
(rule (=> (and (rev $l1 $l2) (append $l2 (cons $x nil) $l3))
          (rev (cons $x $l1) $l3)))

; queries

(declare-rel q1 (list))

(define-fun target-len () Int 9)

(rule (=> (and (len $l1 target-len)
               (rev $l1 $l2)
               (sum $l1 (s (s z)))
               (= $l1 $l2))
          (q1 $l1)))

(query q1 :print-certificate true)
