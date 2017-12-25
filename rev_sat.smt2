; expect: sat

(set-logic ALL)

(declare-datatypes
   ()
   ((list (cons (select_cons_0 Int) (select_cons_1 list)) 
          (nil))))
(define-funs-rec
   ((append ((x list) (y list)) list))
   ((match x (((cons n tail) (cons n (append tail y))) 
              (nil y)))))
(define-funs-rec
   ((rev ((l list)) list))
   ((match l
      (((cons x_1 xs) (append (rev xs) (cons x_1 nil))) 
       (nil nil)))))
(define-funs-rec
   ((size ((l list)) Int))
   ((match l
      (((cons x_1 xs) (+ 1 (size xs)))
       (nil 0)))))
(define-funs-rec
   ((sum ((l list)) Int))
   ((match l
      (((cons x_1 xs) (+ x_1 (sum xs))) 
       (nil 0)))))

(declare-const l_1 list)

(assert (= l_1 (rev l_1)))
(assert (= (size l_1) 3))
(assert (= (sum l_1) 4))
(check-sat)
(get-model)
