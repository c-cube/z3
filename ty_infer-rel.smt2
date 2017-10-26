; expect: SAT

; synthesize a lambda term of type
; "(a -> b) -> (b -> c) -> a -> c"
; from the definition of the type-checking function

; here, a,b,c are type constructors

(declare-datatypes () ((nat (s (select_s_0 nat)) 
                            (z))))
(declare-datatypes
   ()
   ((ty (arrow (select_arrow_0 ty) (select_arrow_1 ty)) 
        (c) 
        (b) 
        (a))))
(declare-datatypes () ((ty_opt (ty_some (select_ty_some_0 ty)) 
                               (ty_none))))
(declare-datatypes
   ()
   ((env (e_cons (select_e_cons_0 ty) (select_e_cons_1 env)) 
         (e_nil))))
(declare-datatypes
   ()
   ((expr
       (app (select_app_0 expr) (select_app_1 expr) (select_app_2 ty)) 
       (lam (select_lam_0 expr)) 
       (var (select_var_0 nat)))))

(declare-var $n nat)
(declare-var $env1 env)
(declare-var $env2 env)
(declare-var $ty1 ty)
(declare-var $ty2 ty)
(declare-var $ty_o ty_opt)
(declare-var $f expr)
(declare-var $x expr)
(declare-var $body expr)

; lookup
(declare-rel at_index (nat env ty_opt))

(rule (at_index z (e_cons $ty1 $env1) (ty_some $ty1)))
(rule (at_index $n e_nil ty_none))
(rule (=> (at_index $n $env1 $ty_o)
          (at_index (s $n) (e_cons $ty1 $env1) $ty_o)))

; ty check
(declare-rel ty_check (env expr ty))

(rule (=> (and (ty_check $env1 $f (arrow $ty1 $ty2))
               (ty_check $env1 $x $ty1))
          (ty_check $env1 (app $f $x $ty1) $ty2)))

(rule (=> (ty_check (e_cons $ty1 $env1) $body $ty2)
          (ty_check $env1 (lam $body) (arrow $ty1 $ty2))))

(rule (=> (at_index $n $env1 (ty_some $ty1))
          (ty_check $env1 (var $n) $ty1)))

; queries

(declare-rel q1 (expr ty))

(rule (=> (ty_check e_nil $x
            (arrow (arrow a b) (arrow a $ty1)))
          (q1 $x $ty1)))

(query q1 :print-certificate true)

(declare-rel q2 (expr))

(rule (=> (ty_check e_nil $x
            (arrow (arrow b c) (arrow (arrow a b) (arrow a c))))
          (q2 $x)))

(query q2 :print-certificate true)
