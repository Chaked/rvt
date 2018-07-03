(set-option
   :int-real-coercions
   false)
(declare-var
   call$1_0_1
   Int)
(declare-var
   call$2_0_1
   Int)
(declare-var
   n$1_0_old_1
   Int)
(declare-var
   n$2_0_old_1
   Int)
(declare-var
   x$1_0_old_1
   Int)
(declare-var
   x$2_0_old_1
   Int)
(declare-rel
   END_QUERY
   ())
(define-fun
   IN_INV
   ((n$1_0 Int)
    (n$2_0 Int))
   Bool
   (= n$1_0 n$2_0))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
(declare-rel
   INV_REC_y__1
   (Int
    Int))
(declare-rel
   INV_REC_y__1_PRE
   (Int))
(declare-rel
   INV_REC_g__2
   (Int
    Int))
(declare-rel
   INV_REC_g__2_PRE
   (Int))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1)
       (n$2_0_1 n$2_0_old_1))
      (let
         ((add$2_0_1 (+ n$2_0_1 1)))
         (=>
            (IN_INV n$1_0_old_1 n$2_0_old_1)
            (INV_REC_g__2_PRE add$2_0_1)))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1)
       (n$2_0_1 n$2_0_old_1))
      (let
         ((add$2_0_1 (+ n$2_0_1 1)))
         (let
            ((result$2_1 call$2_0_1))
            (=>
               (and
                  (IN_INV n$1_0_old_1 n$2_0_old_1)
                  (INV_REC_g__2 add$2_0_1 call$2_0_1))
               (INV_REC_y__1_PRE n$1_0_1))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1)
       (n$2_0_1 n$2_0_old_1))
      (let
         ((add$2_0_1 (+ n$2_0_1 1)))
         (let
            ((result$2_1 call$2_0_1))
            (let
               ((add$1_0_1 (+ call$1_0_1 2)))
               (let
                  ((result$1_1 add$1_0_1))
                  (=>
                     (and
                        (IN_INV n$1_0_old_1 n$2_0_old_1)
                        (INV_REC_g__2 add$2_0_1 call$2_0_1)
                        (INV_REC_y__1 n$1_0_1 call$1_0_1)
                        (not (OUT_INV result$1_1 result$2_1)))
                     END_QUERY)))))))
(rule
   (let
      ((x$1_0_1 x$1_0_old_1))
      (let
         ((result$1_1 x$1_0_1))
         (=>
            (INV_REC_y__1_PRE x$1_0_old_1)
            (INV_REC_y__1 x$1_0_old_1 result$1_1)))))
(rule
   (let
      ((x$2_0_1 x$2_0_old_1))
      (let
         ((result$2_1 x$2_0_1))
         (=>
            (INV_REC_g__2_PRE x$2_0_old_1)
            (INV_REC_g__2 x$2_0_old_1 result$2_1)))))
(query
   END_QUERY
   :print-certificate
   true)
