(set-option
   :int-real-coercions
   false)
(declare-var
   HEAP$1_old_1
   (Array Int Int))
(declare-var
   HEAP$1_res_1
   (Array Int Int))
(declare-var
   HEAP$1_res_2
   (Array Int Int))
(declare-var
   HEAP$1_res_3
   (Array Int Int))
(declare-var
   HEAP$2_old_1
   (Array Int Int))
(declare-var
   HEAP$2_res_1
   (Array Int Int))
(declare-var
   HEAP$2_res_2
   (Array Int Int))
(declare-var
   HEAP$2_res_3
   (Array Int Int))
(declare-var
   SP$1_old_1
   Int)
(declare-var
   SP$2_old_1
   Int)
(declare-var
   STACK$1_old_1
   (Array Int Int))
(declare-var
   STACK$1_res_1
   (Array Int Int))
(declare-var
   STACK$1_res_2
   (Array Int Int))
(declare-var
   STACK$1_res_3
   (Array Int Int))
(declare-var
   STACK$2_old_1
   (Array Int Int))
(declare-var
   STACK$2_res_1
   (Array Int Int))
(declare-var
   STACK$2_res_2
   (Array Int Int))
(declare-var
   STACK$2_res_3
   (Array Int Int))
(declare-var
   a$1_0_OnStack_old_1
   Bool)
(declare-var
   a$1_0_old_1
   Int)
(declare-var
   a$2_0_OnStack_old_1
   Bool)
(declare-var
   a$2_0_old_1
   Int)
(declare-var
   call$1_0_1
   Int)
(declare-var
   call$2_0_1
   Int)
(declare-var
   call1$1_0_1
   Int)
(declare-var
   call1$2_0_1
   Int)
(declare-var
   call2$2_0_1
   Int)
(declare-var
   i$1_0_old_1
   Int)
(declare-var
   i$2_0_old_1
   Int)
(declare-var
   n$1_0_old_1
   Int)
(declare-var
   n$2_0_old_1
   Int)
(declare-var
   res1_1
   Int)
(declare-var
   res2_1
   Int)
(declare-var
   rvp_i$1_0_OnStack_old_1
   Bool)
(declare-var
   rvp_i$1_0_old_1
   Int)
(declare-var
   rvp_i$2_0_OnStack_old_1
   Bool)
(declare-var
   rvp_i$2_0_old_1
   Int)
(declare-var
   rvp_j$1_0_OnStack_old_1
   Bool)
(declare-var
   rvp_j$1_0_old_1
   Int)
(declare-var
   rvp_j$2_0_OnStack_old_1
   Bool)
(declare-var
   rvp_j$2_0_old_1
   Int)
(declare-var
   rvp_rvretval$1_0_OnStack_old_1
   Bool)
(declare-var
   rvp_rvretval$1_0_old_1
   Int)
(declare-var
   rvp_rvretval$2_0_OnStack_old_1
   Bool)
(declare-var
   rvp_rvretval$2_0_old_1
   Int)
(declare-var
   sz$1_0_old_1
   Int)
(declare-var
   sz$2_0_old_1
   Int)
(define-fun
   a$1
   ()
   Int
   (- 101))
(define-fun
   a$2
   ()
   Int
   (- 101))
(declare-rel
   END_QUERY
   ())
(define-fun
   select_
   ((heap (Array Int Int))
    (stack (Array Int Int))
    (pointer Int)
    (onStack Bool))
   Int
   (ite onStack (select stack pointer) (select heap pointer)))
(define-fun
   store_
   ((heap (Array Int Int))
    (stack (Array Int Int))
    (pointer Int)
    (onStack Bool)
    (val Int))
   (Array Int Int)
   (ite onStack (store stack pointer val) (store heap pointer val)))
(define-fun
   INV_REC_rv_mult_int__int_^rv_mult_int__int_
   ((_$1_0 Int)
    (_$1_1 Int)
    (HEAP$1 (Array Int Int))
    (SP$1 Int)
    (STACK$1 (Array Int Int))
    (_$2_0 Int)
    (_$2_1 Int)
    (HEAP$2 (Array Int Int))
    (SP$2 Int)
    (STACK$2 (Array Int Int))
    (result$1 Int)
    (result$2 Int)
    (HEAP$1_res (Array Int Int))
    (HEAP$2_res (Array Int Int))
    (STACK$1_res (Array Int Int))
    (STACK$2_res (Array Int Int)))
   Bool
   (=>
      (and
         (= _$1_0 _$2_0)
         (= _$1_1 _$2_1)
         (= HEAP$1 HEAP$2)
         (= SP$1 SP$2)
         (= STACK$1 STACK$2))
      (and
         (= result$1 result$2)
         (= HEAP$1_res HEAP$2_res)
         (= STACK$1_res STACK$2_res))))
(define-fun
   INV_REC_rv_mult_int__int___1
   ((_$1_0 Int)
    (_$1_1 Int)
    (HEAP (Array Int Int))
    (SP Int)
    (STACK (Array Int Int))
    (result$1 Int)
    (HEAP$1_res (Array Int Int))
    (STACK$1_res (Array Int Int)))
   Bool
   true)
(define-fun
   INV_REC_rv_mult_int__int___2
   ((_$2_0 Int)
    (_$2_1 Int)
    (HEAP (Array Int Int))
    (SP Int)
    (STACK (Array Int Int))
    (result$2 Int)
    (HEAP$2_res (Array Int Int))
    (STACK$2_res (Array Int Int)))
   Bool
   true)
(define-fun
   IN_INV
   ((a$1_0 Int)
    (a$1_0_OnStack Bool)
    (n$1_0 Int)
    (HEAP$1 (Array Int Int))
    (SP$1 Int)
    (STACK$1 (Array Int Int))
    (a$2_0 Int)
    (a$2_0_OnStack Bool)
    (n$2_0 Int)
    (HEAP$2 (Array Int Int))
    (SP$2 Int)
    (STACK$2 (Array Int Int)))
   Bool
   (and
      (= a$1_0 a$2_0)
      (= a$1_0_OnStack a$2_0_OnStack)
      (= n$1_0 n$2_0)
      (= HEAP$1 HEAP$2)
      (= SP$1 SP$2)
      (= STACK$1 STACK$2)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (= HEAP$1 HEAP$2)))
(declare-rel
   INV_REC_bubble_sort^bubble_sort
   (Int
    Bool
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Bool
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Int
    (Array Int Int)
    (Array Int Int)
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_bubble_sort^bubble_sort_PRE
   (Int
    Bool
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Bool
    Int
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1
   (Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Int
    (Array Int Int)
    (Array Int Int)
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE
   (Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1
   (Int
    Bool
    Int
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Bool
    Int
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Int
    (Array Int Int)
    (Array Int Int)
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE
   (Int
    Bool
    Int
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Bool
    Int
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_foo_function_while1^Loop_foo_function_while1
   (Int
    Bool
    Int
    Bool
    Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Bool
    Int
    Int
    Bool
    Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Int
    (Array Int Int)
    (Array Int Int)
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE
   (Int
    Bool
    Int
    Bool
    Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    Bool
    Int
    Int
    Bool
    Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_bubble_sort__1
   (Int
    Bool
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_bubble_sort__1_PRE
   (Int
    Bool
    Int
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1__1
   (Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1__1_PRE
   (Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1_for1__1
   (Int
    Bool
    Int
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1_for1__1_PRE
   (Int
    Bool
    Int
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_foo_function_while1__1
   (Int
    Bool
    Int
    Bool
    Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_foo_function_while1__1_PRE
   (Int
    Bool
    Int
    Bool
    Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_bubble_sort__2
   (Int
    Bool
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_bubble_sort__2_PRE
   (Int
    Bool
    Int
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1__2
   (Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1__2_PRE
   (Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1_for1__2
   (Int
    Bool
    Int
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_bubble_sort_for1_for1__2_PRE
   (Int
    Bool
    Int
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_foo_function_while1__2
   (Int
    Bool
    Int
    Int
    Bool
    Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)
    Int
    (Array Int Int)
    (Array Int Int)))
(declare-rel
   INV_REC_Loop_foo_function_while1__2_PRE
   (Int
    Bool
    Int
    Int
    Bool
    Int
    Bool
    Int
    Bool
    (Array Int Int)
    Int
    (Array Int Int)))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (n$1_0_1 n$1_0_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((rvretval$1_0_1 SP$1_2)
             (rvretval$1_0_OnStack_1 true)
             (SP$1_3 (- SP$1_2 4)))
            (let
               ((i$1_0_1 SP$1_3)
                (i$1_0_OnStack_1 true)
                (SP$1_4 (- SP$1_3 4)))
               (let
                  ((j$1_0_1 SP$1_4)
                   (j$1_0_OnStack_1 true)
                   (HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 rvretval$1_0_1 rvretval$1_0_OnStack_1 0)))
                  (let
                     ((HEAP$1_3 (store_ HEAP$1_2 STACK$1_1 i$1_0_1 i$1_0_OnStack_1 n$1_0_1)))
                     (let
                        ((HEAP$1_4 (store_ HEAP$1_3 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                        (let
                           ((HEAP$1_5 HEAP$1_4)
                            (a$2_0_1 a$2_0_old_1)
                            (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                            (n$2_0_1 n$2_0_old_1)
                            (HEAP$2_1 HEAP$2_old_1)
                            (SP$2_1 SP$2_old_1))
                           (let
                              ((STACK$2_1 STACK$2_old_1)
                               (SP$2_2 (- SP$2_1 4)))
                              (let
                                 ((rvretval$2_0_1 SP$2_2)
                                  (rvretval$2_0_OnStack_1 true)
                                  (SP$2_3 (- SP$2_2 4)))
                                 (let
                                    ((i$2_0_1 SP$2_3)
                                     (i$2_0_OnStack_1 true)
                                     (SP$2_4 (- SP$2_3 4)))
                                    (let
                                       ((j$2_0_1 SP$2_4)
                                        (j$2_0_OnStack_1 true)
                                        (HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 rvretval$2_0_1 rvretval$2_0_OnStack_1 0)))
                                       (let
                                          ((HEAP$2_3 (store_ HEAP$2_2 STACK$2_1 i$2_0_1 i$2_0_OnStack_1 0)))
                                          (let
                                             ((HEAP$2_4 (store_ HEAP$2_3 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                                             (let
                                                ((HEAP$2_5 HEAP$2_4))
                                                (=>
                                                   (IN_INV a$1_0_old_1 a$1_0_OnStack_old_1 n$1_0_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                   (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 i$1_0_OnStack_1 j$1_0_1 j$1_0_OnStack_1 rvretval$1_0_1 rvretval$1_0_OnStack_1 HEAP$1_5 SP$1_4 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 n$2_0_1 i$2_0_1 i$2_0_OnStack_1 j$2_0_1 j$2_0_OnStack_1 rvretval$2_0_1 rvretval$2_0_OnStack_1 HEAP$2_5 SP$2_4 STACK$2_1))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (n$1_0_1 n$1_0_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((rvretval$1_0_1 SP$1_2)
             (rvretval$1_0_OnStack_1 true)
             (SP$1_3 (- SP$1_2 4)))
            (let
               ((i$1_0_1 SP$1_3)
                (i$1_0_OnStack_1 true)
                (SP$1_4 (- SP$1_3 4)))
               (let
                  ((j$1_0_1 SP$1_4)
                   (j$1_0_OnStack_1 true)
                   (HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 rvretval$1_0_1 rvretval$1_0_OnStack_1 0)))
                  (let
                     ((HEAP$1_3 (store_ HEAP$1_2 STACK$1_1 i$1_0_1 i$1_0_OnStack_1 n$1_0_1)))
                     (let
                        ((HEAP$1_4 (store_ HEAP$1_3 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                        (let
                           ((HEAP$1_5 HEAP$1_4)
                            (a$2_0_1 a$2_0_old_1)
                            (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                            (n$2_0_1 n$2_0_old_1)
                            (HEAP$2_1 HEAP$2_old_1)
                            (SP$2_1 SP$2_old_1))
                           (let
                              ((STACK$2_1 STACK$2_old_1)
                               (SP$2_2 (- SP$2_1 4)))
                              (let
                                 ((rvretval$2_0_1 SP$2_2)
                                  (rvretval$2_0_OnStack_1 true)
                                  (SP$2_3 (- SP$2_2 4)))
                                 (let
                                    ((i$2_0_1 SP$2_3)
                                     (i$2_0_OnStack_1 true)
                                     (SP$2_4 (- SP$2_3 4)))
                                    (let
                                       ((j$2_0_1 SP$2_4)
                                        (j$2_0_OnStack_1 true)
                                        (HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 rvretval$2_0_1 rvretval$2_0_OnStack_1 0)))
                                       (let
                                          ((HEAP$2_3 (store_ HEAP$2_2 STACK$2_1 i$2_0_1 i$2_0_OnStack_1 0)))
                                          (let
                                             ((HEAP$2_4 (store_ HEAP$2_3 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                                             (let
                                                ((HEAP$2_5 HEAP$2_4))
                                                (let
                                                   ((HEAP$1_6 HEAP$1_res_1)
                                                    (STACK$1_2 STACK$1_res_1))
                                                   (let
                                                      ((_$1_0_1 (select_ HEAP$1_6 STACK$1_2 j$1_0_1 j$1_0_OnStack_1)))
                                                      (let
                                                         ((result$1_1 _$1_0_1)
                                                          (HEAP$1_res_2 HEAP$1_6)
                                                          (STACK$1_res_2 STACK$1_2)
                                                          (HEAP$2_6 HEAP$2_res_1)
                                                          (STACK$2_2 STACK$2_res_1))
                                                         (let
                                                            ((_$2_0_1 (select_ HEAP$2_6 STACK$2_2 j$2_0_1 j$2_0_OnStack_1)))
                                                            (let
                                                               ((result$2_1 _$2_0_1)
                                                                (HEAP$2_res_2 HEAP$2_6)
                                                                (STACK$2_res_2 STACK$2_2))
                                                               (=>
                                                                  (and
                                                                     (IN_INV a$1_0_old_1 a$1_0_OnStack_old_1 n$1_0_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                     (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 i$1_0_OnStack_1 j$1_0_1 j$1_0_OnStack_1 rvretval$1_0_1 rvretval$1_0_OnStack_1 HEAP$1_5 SP$1_4 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 n$2_0_1 i$2_0_1 i$2_0_OnStack_1 j$2_0_1 j$2_0_OnStack_1 rvretval$2_0_1 rvretval$2_0_OnStack_1 HEAP$2_5 SP$2_4 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1)
                                                                     (not (OUT_INV result$1_1 result$2_1 HEAP$1_6 HEAP$2_6)))
                                                                  END_QUERY))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (sz$1_0_1 sz$1_0_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((i$1_0_1 SP$1_2)
             (i$1_0_OnStack_1 true)
             (sub$1_0_1 (- sz$1_0_1 1)))
            (let
               ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 i$1_0_1 i$1_0_OnStack_1 sub$1_0_1)))
               (let
                  ((HEAP$1_3 HEAP$1_2)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (sz$2_0_1 sz$2_0_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1))
                  (let
                     ((STACK$2_1 STACK$2_old_1)
                      (SP$2_2 (- SP$2_1 4)))
                     (let
                        ((i$2_0_1 SP$2_2)
                         (i$2_0_OnStack_1 true)
                         (sub$2_0_1 (- sz$2_0_1 1)))
                        (let
                           ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 i$2_0_1 i$2_0_OnStack_1 sub$2_0_1)))
                           (let
                              ((HEAP$2_3 HEAP$2_2))
                              (=>
                                 (INV_REC_bubble_sort^bubble_sort_PRE a$1_0_old_1 a$1_0_OnStack_old_1 sz$1_0_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 sz$2_0_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                 (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 i$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 i$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (sz$1_0_1 sz$1_0_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((i$1_0_1 SP$1_2)
             (i$1_0_OnStack_1 true)
             (sub$1_0_1 (- sz$1_0_1 1)))
            (let
               ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 i$1_0_1 i$1_0_OnStack_1 sub$1_0_1)))
               (let
                  ((HEAP$1_3 HEAP$1_2)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (sz$2_0_1 sz$2_0_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1))
                  (let
                     ((STACK$2_1 STACK$2_old_1)
                      (SP$2_2 (- SP$2_1 4)))
                     (let
                        ((i$2_0_1 SP$2_2)
                         (i$2_0_OnStack_1 true)
                         (sub$2_0_1 (- sz$2_0_1 1)))
                        (let
                           ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 i$2_0_1 i$2_0_OnStack_1 sub$2_0_1)))
                           (let
                              ((HEAP$2_3 HEAP$2_2))
                              (let
                                 ((HEAP$1_4 HEAP$1_res_1)
                                  (STACK$1_2 STACK$1_res_1))
                                 (let
                                    ((result$1_1 0)
                                     (HEAP$1_res_2 HEAP$1_4)
                                     (STACK$1_res_2 STACK$1_2)
                                     (HEAP$2_4 HEAP$2_res_1)
                                     (STACK$2_2 STACK$2_res_1))
                                    (let
                                       ((result$2_1 0)
                                        (HEAP$2_res_2 HEAP$2_4)
                                        (STACK$2_res_2 STACK$2_2))
                                       (=>
                                          (and
                                             (INV_REC_bubble_sort^bubble_sort_PRE a$1_0_old_1 a$1_0_OnStack_old_1 sz$1_0_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 sz$2_0_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                             (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 i$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 i$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1))
                                          (INV_REC_bubble_sort^bubble_sort a$1_0_old_1 a$1_0_OnStack_old_1 sz$1_0_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 sz$2_0_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_2 HEAP$2_res_2 STACK$1_res_2 STACK$2_res_2)))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                  (let
                     ((_$1_1_1 (select_ HEAP$1_2 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1))
                      (HEAP$1_3 HEAP$1_2)
                      (a$2_0_1 a$2_0_old_1)
                      (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                      (rvp_i$2_0_1 rvp_i$2_0_old_1)
                      (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                      (HEAP$2_1 HEAP$2_old_1)
                      (SP$2_1 SP$2_old_1))
                     (let
                        ((STACK$2_1 STACK$2_old_1)
                         (SP$2_2 (- SP$2_1 4)))
                        (let
                           ((j$2_0_1 SP$2_2)
                            (j$2_0_OnStack_1 true)
                            (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((cmp$2_0_1 (> _$2_0_1 0)))
                              (let
                                 ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                                 (let
                                    ((_$2_1_1 (select_ HEAP$2_2 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1))
                                     (HEAP$2_3 HEAP$2_2))
                                    (=>
                                       (and
                                          (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                          cmp$1_0_1
                                          cmp$2_0_1)
                                       (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_1 a$1_0_OnStack_1 _$1_1_1 j$1_0_1 j$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 _$2_1_1 j$2_0_1 j$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                  (let
                     ((_$1_1_1 (select_ HEAP$1_2 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1))
                      (HEAP$1_3 HEAP$1_2)
                      (a$2_0_1 a$2_0_old_1)
                      (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                      (rvp_i$2_0_1 rvp_i$2_0_old_1)
                      (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                      (HEAP$2_1 HEAP$2_old_1)
                      (SP$2_1 SP$2_old_1))
                     (let
                        ((STACK$2_1 STACK$2_old_1)
                         (SP$2_2 (- SP$2_1 4)))
                        (let
                           ((j$2_0_1 SP$2_2)
                            (j$2_0_OnStack_1 true)
                            (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((cmp$2_0_1 (> _$2_0_1 0)))
                              (let
                                 ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                                 (let
                                    ((_$2_1_1 (select_ HEAP$2_2 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1))
                                     (HEAP$2_3 HEAP$2_2))
                                    (let
                                       ((HEAP$1_4 HEAP$1_res_1)
                                        (STACK$1_2 STACK$1_res_1))
                                       (let
                                          ((_$1_2_1 (select_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                                          (let
                                             ((sub$1_0_1 (- _$1_2_1 1)))
                                             (let
                                                ((HEAP$1_5 (store_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                                (let
                                                   ((HEAP$1_6 HEAP$1_5)
                                                    (HEAP$2_4 HEAP$2_res_1)
                                                    (STACK$2_2 STACK$2_res_1))
                                                   (let
                                                      ((_$2_2_1 (select_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                                                      (let
                                                         ((dec$2_0_1 (+ _$2_2_1 (- 1))))
                                                         (let
                                                            ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 dec$2_0_1)))
                                                            (let
                                                               ((HEAP$2_6 HEAP$2_5))
                                                               (=>
                                                                  (and
                                                                     (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                     cmp$1_0_1
                                                                     cmp$2_0_1
                                                                     (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_1 a$1_0_OnStack_1 _$1_1_1 j$1_0_1 j$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 _$2_1_1 j$2_0_1 j$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1))
                                                                  (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 HEAP$1_6 SP$1_2 STACK$1_2 a$2_0_1 a$2_0_OnStack_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 HEAP$2_6 SP$2_2 STACK$2_2)))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                  (let
                     ((_$1_1_1 (select_ HEAP$1_2 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1))
                      (HEAP$1_3 HEAP$1_2)
                      (a$2_0_1 a$2_0_old_1)
                      (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                      (rvp_i$2_0_1 rvp_i$2_0_old_1)
                      (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                      (HEAP$2_1 HEAP$2_old_1)
                      (SP$2_1 SP$2_old_1))
                     (let
                        ((STACK$2_1 STACK$2_old_1)
                         (SP$2_2 (- SP$2_1 4)))
                        (let
                           ((j$2_0_1 SP$2_2)
                            (j$2_0_OnStack_1 true)
                            (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((cmp$2_0_1 (> _$2_0_1 0)))
                              (let
                                 ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                                 (let
                                    ((_$2_1_1 (select_ HEAP$2_2 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1))
                                     (HEAP$2_3 HEAP$2_2))
                                    (let
                                       ((HEAP$1_4 HEAP$1_res_1)
                                        (STACK$1_2 STACK$1_res_1))
                                       (let
                                          ((_$1_2_1 (select_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                                          (let
                                             ((sub$1_0_1 (- _$1_2_1 1)))
                                             (let
                                                ((HEAP$1_5 (store_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                                (let
                                                   ((HEAP$1_6 HEAP$1_5)
                                                    (HEAP$2_4 HEAP$2_res_1)
                                                    (STACK$2_2 STACK$2_res_1))
                                                   (let
                                                      ((_$2_2_1 (select_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                                                      (let
                                                         ((dec$2_0_1 (+ _$2_2_1 (- 1))))
                                                         (let
                                                            ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 dec$2_0_1)))
                                                            (let
                                                               ((HEAP$2_6 HEAP$2_5))
                                                               (let
                                                                  ((HEAP$1_7 HEAP$1_res_2)
                                                                   (STACK$1_3 STACK$1_res_2)
                                                                   (retval.0$1_0_1 call1$1_0_1))
                                                                  (let
                                                                     ((result$1_1 retval.0$1_0_1)
                                                                      (HEAP$1_res_3 HEAP$1_7)
                                                                      (STACK$1_res_3 STACK$1_3)
                                                                      (HEAP$2_7 HEAP$2_res_2)
                                                                      (STACK$2_3 STACK$2_res_2)
                                                                      (retval.0$2_0_1 call1$2_0_1))
                                                                     (let
                                                                        ((result$2_1 retval.0$2_0_1)
                                                                         (HEAP$2_res_3 HEAP$2_7)
                                                                         (STACK$2_res_3 STACK$2_3))
                                                                        (=>
                                                                           (and
                                                                              (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                              cmp$1_0_1
                                                                              cmp$2_0_1
                                                                              (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_1 a$1_0_OnStack_1 _$1_1_1 j$1_0_1 j$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 _$2_1_1 j$2_0_1 j$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1)
                                                                              (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1 a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 HEAP$1_6 SP$1_2 STACK$1_2 a$2_0_1 a$2_0_OnStack_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 HEAP$2_6 SP$2_2 STACK$2_2 call1$1_0_1 call1$2_0_1 HEAP$1_res_2 HEAP$2_res_2 STACK$1_res_2 STACK$2_res_2))
                                                                           (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_3 HEAP$2_res_3 STACK$1_res_3 STACK$2_res_3))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                  (let
                     ((_$1_1_1 (select_ HEAP$1_2 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1))
                      (HEAP$1_3 HEAP$1_2)
                      (a$2_0_1 a$2_0_old_1)
                      (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                      (rvp_i$2_0_1 rvp_i$2_0_old_1)
                      (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                      (HEAP$2_1 HEAP$2_old_1)
                      (SP$2_1 SP$2_old_1))
                     (let
                        ((STACK$2_1 STACK$2_old_1)
                         (SP$2_2 (- SP$2_1 4)))
                        (let
                           ((j$2_0_1 SP$2_2)
                            (j$2_0_OnStack_1 true)
                            (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((cmp$2_0_1 (> _$2_0_1 0)))
                              (let
                                 ((retval.0$2_0_1 0))
                                 (let
                                    ((result$2_1 retval.0$2_0_1)
                                     (HEAP$2_res_1 HEAP$2_1)
                                     (STACK$2_res_1 STACK$2_1))
                                    (=>
                                       (and
                                          (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                          cmp$1_0_1
                                          (not cmp$2_0_1))
                                       (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_1 a$1_0_OnStack_1 _$1_1_1 j$1_0_1 j$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                  (let
                     ((_$1_1_1 (select_ HEAP$1_2 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1))
                      (HEAP$1_3 HEAP$1_2)
                      (a$2_0_1 a$2_0_old_1)
                      (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                      (rvp_i$2_0_1 rvp_i$2_0_old_1)
                      (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                      (HEAP$2_1 HEAP$2_old_1)
                      (SP$2_1 SP$2_old_1))
                     (let
                        ((STACK$2_1 STACK$2_old_1)
                         (SP$2_2 (- SP$2_1 4)))
                        (let
                           ((j$2_0_1 SP$2_2)
                            (j$2_0_OnStack_1 true)
                            (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((cmp$2_0_1 (> _$2_0_1 0)))
                              (let
                                 ((retval.0$2_0_1 0))
                                 (let
                                    ((result$2_1 retval.0$2_0_1)
                                     (HEAP$2_res_1 HEAP$2_1)
                                     (STACK$2_res_1 STACK$2_1))
                                    (let
                                       ((HEAP$1_4 HEAP$1_res_1)
                                        (STACK$1_2 STACK$1_res_1))
                                       (let
                                          ((_$1_2_1 (select_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                                          (let
                                             ((sub$1_0_1 (- _$1_2_1 1)))
                                             (let
                                                ((HEAP$1_5 (store_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                                (let
                                                   ((HEAP$1_6 HEAP$1_5))
                                                   (=>
                                                      (and
                                                         (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                         cmp$1_0_1
                                                         (not cmp$2_0_1)
                                                         (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_1 a$1_0_OnStack_1 _$1_1_1 j$1_0_1 j$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1))
                                                      (INV_REC_Loop_bubble_sort_for1__1_PRE a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 HEAP$1_6 SP$1_2 STACK$1_2)))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                  (let
                     ((_$1_1_1 (select_ HEAP$1_2 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1))
                      (HEAP$1_3 HEAP$1_2)
                      (a$2_0_1 a$2_0_old_1)
                      (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                      (rvp_i$2_0_1 rvp_i$2_0_old_1)
                      (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                      (HEAP$2_1 HEAP$2_old_1)
                      (SP$2_1 SP$2_old_1))
                     (let
                        ((STACK$2_1 STACK$2_old_1)
                         (SP$2_2 (- SP$2_1 4)))
                        (let
                           ((j$2_0_1 SP$2_2)
                            (j$2_0_OnStack_1 true)
                            (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((cmp$2_0_1 (> _$2_0_1 0)))
                              (let
                                 ((retval.0$2_0_1 0))
                                 (let
                                    ((result$2_1 retval.0$2_0_1)
                                     (HEAP$2_res_1 HEAP$2_1)
                                     (STACK$2_res_1 STACK$2_1))
                                    (let
                                       ((HEAP$1_4 HEAP$1_res_1)
                                        (STACK$1_2 STACK$1_res_1))
                                       (let
                                          ((_$1_2_1 (select_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                                          (let
                                             ((sub$1_0_1 (- _$1_2_1 1)))
                                             (let
                                                ((HEAP$1_5 (store_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                                (let
                                                   ((HEAP$1_6 HEAP$1_5))
                                                   (let
                                                      ((HEAP$1_7 HEAP$1_res_2)
                                                       (STACK$1_3 STACK$1_res_2)
                                                       (retval.0$1_0_1 call1$1_0_1))
                                                      (let
                                                         ((result$1_1 retval.0$1_0_1)
                                                          (HEAP$1_res_3 HEAP$1_7)
                                                          (STACK$1_res_3 STACK$1_3))
                                                         (=>
                                                            (and
                                                               (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                               cmp$1_0_1
                                                               (not cmp$2_0_1)
                                                               (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_1 a$1_0_OnStack_1 _$1_1_1 j$1_0_1 j$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1)
                                                               (INV_REC_Loop_bubble_sort_for1__1 a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 HEAP$1_6 SP$1_2 STACK$1_2 call1$1_0_1 HEAP$1_res_2 STACK$1_res_2))
                                                            (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_3 HEAP$2_res_1 STACK$1_res_3 STACK$2_res_1)))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((retval.0$1_0_1 0))
                  (let
                     ((result$1_1 retval.0$1_0_1)
                      (HEAP$1_res_1 HEAP$1_1)
                      (STACK$1_res_1 STACK$1_1)
                      (a$2_0_1 a$2_0_old_1)
                      (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                      (rvp_i$2_0_1 rvp_i$2_0_old_1)
                      (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                      (HEAP$2_1 HEAP$2_old_1)
                      (SP$2_1 SP$2_old_1))
                     (let
                        ((STACK$2_1 STACK$2_old_1)
                         (SP$2_2 (- SP$2_1 4)))
                        (let
                           ((j$2_0_1 SP$2_2)
                            (j$2_0_OnStack_1 true)
                            (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((cmp$2_0_1 (> _$2_0_1 0)))
                              (let
                                 ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                                 (let
                                    ((_$2_1_1 (select_ HEAP$2_2 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1))
                                     (HEAP$2_3 HEAP$2_2))
                                    (=>
                                       (and
                                          (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                          (not cmp$1_0_1)
                                          cmp$2_0_1)
                                       (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_1 a$2_0_OnStack_1 _$2_1_1 j$2_0_1 j$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((retval.0$1_0_1 0))
                  (let
                     ((result$1_1 retval.0$1_0_1)
                      (HEAP$1_res_1 HEAP$1_1)
                      (STACK$1_res_1 STACK$1_1)
                      (a$2_0_1 a$2_0_old_1)
                      (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                      (rvp_i$2_0_1 rvp_i$2_0_old_1)
                      (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                      (HEAP$2_1 HEAP$2_old_1)
                      (SP$2_1 SP$2_old_1))
                     (let
                        ((STACK$2_1 STACK$2_old_1)
                         (SP$2_2 (- SP$2_1 4)))
                        (let
                           ((j$2_0_1 SP$2_2)
                            (j$2_0_OnStack_1 true)
                            (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((cmp$2_0_1 (> _$2_0_1 0)))
                              (let
                                 ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                                 (let
                                    ((_$2_1_1 (select_ HEAP$2_2 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1))
                                     (HEAP$2_3 HEAP$2_2))
                                    (let
                                       ((HEAP$2_4 HEAP$2_res_1)
                                        (STACK$2_2 STACK$2_res_1))
                                       (let
                                          ((_$2_2_1 (select_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                                          (let
                                             ((dec$2_0_1 (+ _$2_2_1 (- 1))))
                                             (let
                                                ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 dec$2_0_1)))
                                                (let
                                                   ((HEAP$2_6 HEAP$2_5))
                                                   (=>
                                                      (and
                                                         (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                         (not cmp$1_0_1)
                                                         cmp$2_0_1
                                                         (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_1 a$2_0_OnStack_1 _$2_1_1 j$2_0_1 j$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1))
                                                      (INV_REC_Loop_bubble_sort_for1__2_PRE a$2_0_1 a$2_0_OnStack_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 HEAP$2_6 SP$2_2 STACK$2_2)))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((retval.0$1_0_1 0))
                  (let
                     ((result$1_1 retval.0$1_0_1)
                      (HEAP$1_res_1 HEAP$1_1)
                      (STACK$1_res_1 STACK$1_1)
                      (a$2_0_1 a$2_0_old_1)
                      (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                      (rvp_i$2_0_1 rvp_i$2_0_old_1)
                      (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                      (HEAP$2_1 HEAP$2_old_1)
                      (SP$2_1 SP$2_old_1))
                     (let
                        ((STACK$2_1 STACK$2_old_1)
                         (SP$2_2 (- SP$2_1 4)))
                        (let
                           ((j$2_0_1 SP$2_2)
                            (j$2_0_OnStack_1 true)
                            (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((cmp$2_0_1 (> _$2_0_1 0)))
                              (let
                                 ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                                 (let
                                    ((_$2_1_1 (select_ HEAP$2_2 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1))
                                     (HEAP$2_3 HEAP$2_2))
                                    (let
                                       ((HEAP$2_4 HEAP$2_res_1)
                                        (STACK$2_2 STACK$2_res_1))
                                       (let
                                          ((_$2_2_1 (select_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                                          (let
                                             ((dec$2_0_1 (+ _$2_2_1 (- 1))))
                                             (let
                                                ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 dec$2_0_1)))
                                                (let
                                                   ((HEAP$2_6 HEAP$2_5))
                                                   (let
                                                      ((HEAP$2_7 HEAP$2_res_2)
                                                       (STACK$2_3 STACK$2_res_2)
                                                       (retval.0$2_0_1 call1$2_0_1))
                                                      (let
                                                         ((result$2_1 retval.0$2_0_1)
                                                          (HEAP$2_res_3 HEAP$2_7)
                                                          (STACK$2_res_3 STACK$2_3))
                                                         (=>
                                                            (and
                                                               (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                               (not cmp$1_0_1)
                                                               cmp$2_0_1
                                                               (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_1 a$2_0_OnStack_1 _$2_1_1 j$2_0_1 j$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1)
                                                               (INV_REC_Loop_bubble_sort_for1__2 a$2_0_1 a$2_0_OnStack_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 HEAP$2_6 SP$2_2 STACK$2_2 call1$2_0_1 HEAP$2_res_2 STACK$2_res_2))
                                                            (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_1 HEAP$2_res_3 STACK$1_res_1 STACK$2_res_3)))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((retval.0$1_0_1 0))
                  (let
                     ((result$1_1 retval.0$1_0_1)
                      (HEAP$1_res_1 HEAP$1_1)
                      (STACK$1_res_1 STACK$1_1)
                      (a$2_0_1 a$2_0_old_1)
                      (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                      (rvp_i$2_0_1 rvp_i$2_0_old_1)
                      (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                      (HEAP$2_1 HEAP$2_old_1)
                      (SP$2_1 SP$2_old_1))
                     (let
                        ((STACK$2_1 STACK$2_old_1)
                         (SP$2_2 (- SP$2_1 4)))
                        (let
                           ((j$2_0_1 SP$2_2)
                            (j$2_0_OnStack_1 true)
                            (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((cmp$2_0_1 (> _$2_0_1 0)))
                              (let
                                 ((retval.0$2_0_1 0))
                                 (let
                                    ((result$2_1 retval.0$2_0_1)
                                     (HEAP$2_res_1 HEAP$2_1)
                                     (STACK$2_res_1 STACK$2_1))
                                    (=>
                                       (and
                                          (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                          (not cmp$1_0_1)
                                          (not cmp$2_0_1))
                                       (INV_REC_Loop_bubble_sort_for1^Loop_bubble_sort_for1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_5_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((idx.ext6$1_0_1 _$1_5_1))
                                             (let
                                                ((add.ptr7$1_0_1 (+ a$1_0_1 (* 4 idx.ext6$1_0_1)))
                                                 (add.ptr7$1_0_OnStack_1 a$1_0_OnStack_1))
                                                (let
                                                   ((_$1_6_1 (select_ HEAP$1_1 STACK$1_1 add.ptr7$1_0_1 add.ptr7$1_0_OnStack_1))
                                                    (_$1_7_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                   (let
                                                      ((idx.ext8$1_0_1 _$1_7_1))
                                                      (let
                                                         ((add.ptr9$1_0_1 (+ a$1_0_1 (* 4 idx.ext8$1_0_1)))
                                                          (add.ptr9$1_0_OnStack_1 a$1_0_OnStack_1))
                                                         (let
                                                            ((add.ptr10$1_0_1 (+ add.ptr9$1_0_1 (* 4 1)))
                                                             (add.ptr10$1_0_OnStack_1 add.ptr9$1_0_OnStack_1))
                                                            (let
                                                               ((_$1_8_1 (select_ HEAP$1_1 STACK$1_1 add.ptr10$1_0_1 add.ptr10$1_0_OnStack_1))
                                                                (_$1_9_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                               (let
                                                                  ((idx.ext11$1_0_1 _$1_9_1))
                                                                  (let
                                                                     ((add.ptr12$1_0_1 (+ a$1_0_1 (* 4 idx.ext11$1_0_1)))
                                                                      (add.ptr12$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                     (let
                                                                        ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 add.ptr12$1_0_1 add.ptr12$1_0_OnStack_1 _$1_8_1)))
                                                                        (let
                                                                           ((_$1_10_1 (select_ HEAP$1_2 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                           (let
                                                                              ((idx.ext13$1_0_1 _$1_10_1))
                                                                              (let
                                                                                 ((add.ptr14$1_0_1 (+ a$1_0_1 (* 4 idx.ext13$1_0_1)))
                                                                                  (add.ptr14$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                                 (let
                                                                                    ((add.ptr15$1_0_1 (+ add.ptr14$1_0_1 (* 4 1)))
                                                                                     (add.ptr15$1_0_OnStack_1 add.ptr14$1_0_OnStack_1))
                                                                                    (let
                                                                                       ((HEAP$1_3 (store_ HEAP$1_2 STACK$1_1 add.ptr15$1_0_1 add.ptr15$1_0_OnStack_1 _$1_6_1)))
                                                                                       (let
                                                                                          ((_$1_11_1 (select_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                                          (let
                                                                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                                                                             (let
                                                                                                ((HEAP$1_4 (store_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                                                                (let
                                                                                                   ((HEAP$1_5 HEAP$1_4)
                                                                                                    (a$2_0_1 a$2_0_old_1)
                                                                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                                                                    (i$2_0_1 i$2_0_old_1)
                                                                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                                                                    (HEAP$2_1 HEAP$2_old_1)
                                                                                                    (SP$2_1 SP$2_old_1)
                                                                                                    (STACK$2_1 STACK$2_old_1))
                                                                                                   (let
                                                                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                      (let
                                                                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                                                                         (let
                                                                                                            ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                            (let
                                                                                                               ((idxprom$2_0_1 _$2_1_1))
                                                                                                               (let
                                                                                                                  ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                                                                                                   (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                  (let
                                                                                                                     ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                                                                                                      (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                     (let
                                                                                                                        ((add$2_0_1 (+ _$2_3_1 1)))
                                                                                                                        (let
                                                                                                                           ((idxprom1$2_0_1 add$2_0_1))
                                                                                                                           (let
                                                                                                                              ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                                                                                                               (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                              (let
                                                                                                                                 ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                                                                                                 (let
                                                                                                                                    ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                                                                                                    (let
                                                                                                                                       ((_$2_5_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                       (let
                                                                                                                                          ((idxprom5$2_0_1 _$2_5_1))
                                                                                                                                          (let
                                                                                                                                             ((arrayidx6$2_0_1 (+ a$2_0_1 (* 4 idxprom5$2_0_1)))
                                                                                                                                              (arrayidx6$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                             (let
                                                                                                                                                ((_$2_6_1 (select_ HEAP$2_1 STACK$2_1 arrayidx6$2_0_1 arrayidx6$2_0_OnStack_1))
                                                                                                                                                 (_$2_7_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                (let
                                                                                                                                                   ((add7$2_0_1 (+ _$2_7_1 1)))
                                                                                                                                                   (let
                                                                                                                                                      ((idxprom8$2_0_1 add7$2_0_1))
                                                                                                                                                      (let
                                                                                                                                                         ((arrayidx9$2_0_1 (+ a$2_0_1 (* 4 idxprom8$2_0_1)))
                                                                                                                                                          (arrayidx9$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_8_1 (select_ HEAP$2_1 STACK$2_1 arrayidx9$2_0_1 arrayidx9$2_0_OnStack_1))
                                                                                                                                                             (_$2_9_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                            (let
                                                                                                                                                               ((idxprom10$2_0_1 _$2_9_1))
                                                                                                                                                               (let
                                                                                                                                                                  ((arrayidx11$2_0_1 (+ a$2_0_1 (* 4 idxprom10$2_0_1)))
                                                                                                                                                                   (arrayidx11$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                                  (let
                                                                                                                                                                     ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 arrayidx11$2_0_1 arrayidx11$2_0_OnStack_1 _$2_8_1)))
                                                                                                                                                                     (let
                                                                                                                                                                        ((_$2_10_1 (select_ HEAP$2_2 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                                        (let
                                                                                                                                                                           ((add12$2_0_1 (+ _$2_10_1 1)))
                                                                                                                                                                           (let
                                                                                                                                                                              ((idxprom13$2_0_1 add12$2_0_1))
                                                                                                                                                                              (let
                                                                                                                                                                                 ((arrayidx14$2_0_1 (+ a$2_0_1 (* 4 idxprom13$2_0_1)))
                                                                                                                                                                                  (arrayidx14$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                                                 (let
                                                                                                                                                                                    ((HEAP$2_3 (store_ HEAP$2_2 STACK$2_1 arrayidx14$2_0_1 arrayidx14$2_0_OnStack_1 _$2_6_1)))
                                                                                                                                                                                    (let
                                                                                                                                                                                       ((_$2_11_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                                                       (let
                                                                                                                                                                                          ((idxprom15$2_0_1 _$2_11_1))
                                                                                                                                                                                          (let
                                                                                                                                                                                             ((arrayidx16$2_0_1 (+ a$2_0_1 (* 4 idxprom15$2_0_1)))
                                                                                                                                                                                              (arrayidx16$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                                                             (let
                                                                                                                                                                                                ((_$2_12_1 (select_ HEAP$2_3 STACK$2_1 arrayidx16$2_0_1 arrayidx16$2_0_OnStack_1))
                                                                                                                                                                                                 (_$2_13_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                                                                (let
                                                                                                                                                                                                   ((idxprom17$2_0_1 _$2_13_1))
                                                                                                                                                                                                   (let
                                                                                                                                                                                                      ((arrayidx18$2_0_1 (+ a$2_0_1 (* 4 idxprom17$2_0_1)))
                                                                                                                                                                                                       (arrayidx18$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                         ((HEAP$2_4 (store_ HEAP$2_3 STACK$2_1 arrayidx18$2_0_1 arrayidx18$2_0_OnStack_1 _$2_12_1)))
                                                                                                                                                                                                         (let
                                                                                                                                                                                                            ((_$2_14_1 (select_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                               ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                                                                                                                                               (let
                                                                                                                                                                                                                  ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                                                                                                                                                  (let
                                                                                                                                                                                                                     ((HEAP$2_6 HEAP$2_5))
                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                        (and
                                                                                                                                                                                                                           (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                                                                                                                           cmp$1_0_1
                                                                                                                                                                                                                           cmp4$1_0_1
                                                                                                                                                                                                                           cmp$2_0_1
                                                                                                                                                                                                                           cmp3$2_0_1)
                                                                                                                                                                                                                        (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_5 SP$1_1 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_6 SP$2_1 STACK$2_1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_5_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((idx.ext6$1_0_1 _$1_5_1))
                                             (let
                                                ((add.ptr7$1_0_1 (+ a$1_0_1 (* 4 idx.ext6$1_0_1)))
                                                 (add.ptr7$1_0_OnStack_1 a$1_0_OnStack_1))
                                                (let
                                                   ((_$1_6_1 (select_ HEAP$1_1 STACK$1_1 add.ptr7$1_0_1 add.ptr7$1_0_OnStack_1))
                                                    (_$1_7_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                   (let
                                                      ((idx.ext8$1_0_1 _$1_7_1))
                                                      (let
                                                         ((add.ptr9$1_0_1 (+ a$1_0_1 (* 4 idx.ext8$1_0_1)))
                                                          (add.ptr9$1_0_OnStack_1 a$1_0_OnStack_1))
                                                         (let
                                                            ((add.ptr10$1_0_1 (+ add.ptr9$1_0_1 (* 4 1)))
                                                             (add.ptr10$1_0_OnStack_1 add.ptr9$1_0_OnStack_1))
                                                            (let
                                                               ((_$1_8_1 (select_ HEAP$1_1 STACK$1_1 add.ptr10$1_0_1 add.ptr10$1_0_OnStack_1))
                                                                (_$1_9_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                               (let
                                                                  ((idx.ext11$1_0_1 _$1_9_1))
                                                                  (let
                                                                     ((add.ptr12$1_0_1 (+ a$1_0_1 (* 4 idx.ext11$1_0_1)))
                                                                      (add.ptr12$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                     (let
                                                                        ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 add.ptr12$1_0_1 add.ptr12$1_0_OnStack_1 _$1_8_1)))
                                                                        (let
                                                                           ((_$1_10_1 (select_ HEAP$1_2 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                           (let
                                                                              ((idx.ext13$1_0_1 _$1_10_1))
                                                                              (let
                                                                                 ((add.ptr14$1_0_1 (+ a$1_0_1 (* 4 idx.ext13$1_0_1)))
                                                                                  (add.ptr14$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                                 (let
                                                                                    ((add.ptr15$1_0_1 (+ add.ptr14$1_0_1 (* 4 1)))
                                                                                     (add.ptr15$1_0_OnStack_1 add.ptr14$1_0_OnStack_1))
                                                                                    (let
                                                                                       ((HEAP$1_3 (store_ HEAP$1_2 STACK$1_1 add.ptr15$1_0_1 add.ptr15$1_0_OnStack_1 _$1_6_1)))
                                                                                       (let
                                                                                          ((_$1_11_1 (select_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                                          (let
                                                                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                                                                             (let
                                                                                                ((HEAP$1_4 (store_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                                                                (let
                                                                                                   ((HEAP$1_5 HEAP$1_4)
                                                                                                    (a$2_0_1 a$2_0_old_1)
                                                                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                                                                    (i$2_0_1 i$2_0_old_1)
                                                                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                                                                    (HEAP$2_1 HEAP$2_old_1)
                                                                                                    (SP$2_1 SP$2_old_1)
                                                                                                    (STACK$2_1 STACK$2_old_1))
                                                                                                   (let
                                                                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                      (let
                                                                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                                                                         (let
                                                                                                            ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                            (let
                                                                                                               ((idxprom$2_0_1 _$2_1_1))
                                                                                                               (let
                                                                                                                  ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                                                                                                   (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                  (let
                                                                                                                     ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                                                                                                      (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                     (let
                                                                                                                        ((add$2_0_1 (+ _$2_3_1 1)))
                                                                                                                        (let
                                                                                                                           ((idxprom1$2_0_1 add$2_0_1))
                                                                                                                           (let
                                                                                                                              ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                                                                                                               (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                              (let
                                                                                                                                 ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                                                                                                 (let
                                                                                                                                    ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                                                                                                    (let
                                                                                                                                       ((_$2_5_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                       (let
                                                                                                                                          ((idxprom5$2_0_1 _$2_5_1))
                                                                                                                                          (let
                                                                                                                                             ((arrayidx6$2_0_1 (+ a$2_0_1 (* 4 idxprom5$2_0_1)))
                                                                                                                                              (arrayidx6$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                             (let
                                                                                                                                                ((_$2_6_1 (select_ HEAP$2_1 STACK$2_1 arrayidx6$2_0_1 arrayidx6$2_0_OnStack_1))
                                                                                                                                                 (_$2_7_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                (let
                                                                                                                                                   ((add7$2_0_1 (+ _$2_7_1 1)))
                                                                                                                                                   (let
                                                                                                                                                      ((idxprom8$2_0_1 add7$2_0_1))
                                                                                                                                                      (let
                                                                                                                                                         ((arrayidx9$2_0_1 (+ a$2_0_1 (* 4 idxprom8$2_0_1)))
                                                                                                                                                          (arrayidx9$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_8_1 (select_ HEAP$2_1 STACK$2_1 arrayidx9$2_0_1 arrayidx9$2_0_OnStack_1))
                                                                                                                                                             (_$2_9_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                            (let
                                                                                                                                                               ((idxprom10$2_0_1 _$2_9_1))
                                                                                                                                                               (let
                                                                                                                                                                  ((arrayidx11$2_0_1 (+ a$2_0_1 (* 4 idxprom10$2_0_1)))
                                                                                                                                                                   (arrayidx11$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                                  (let
                                                                                                                                                                     ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 arrayidx11$2_0_1 arrayidx11$2_0_OnStack_1 _$2_8_1)))
                                                                                                                                                                     (let
                                                                                                                                                                        ((_$2_10_1 (select_ HEAP$2_2 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                                        (let
                                                                                                                                                                           ((add12$2_0_1 (+ _$2_10_1 1)))
                                                                                                                                                                           (let
                                                                                                                                                                              ((idxprom13$2_0_1 add12$2_0_1))
                                                                                                                                                                              (let
                                                                                                                                                                                 ((arrayidx14$2_0_1 (+ a$2_0_1 (* 4 idxprom13$2_0_1)))
                                                                                                                                                                                  (arrayidx14$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                                                 (let
                                                                                                                                                                                    ((HEAP$2_3 (store_ HEAP$2_2 STACK$2_1 arrayidx14$2_0_1 arrayidx14$2_0_OnStack_1 _$2_6_1)))
                                                                                                                                                                                    (let
                                                                                                                                                                                       ((_$2_11_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                                                       (let
                                                                                                                                                                                          ((idxprom15$2_0_1 _$2_11_1))
                                                                                                                                                                                          (let
                                                                                                                                                                                             ((arrayidx16$2_0_1 (+ a$2_0_1 (* 4 idxprom15$2_0_1)))
                                                                                                                                                                                              (arrayidx16$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                                                             (let
                                                                                                                                                                                                ((_$2_12_1 (select_ HEAP$2_3 STACK$2_1 arrayidx16$2_0_1 arrayidx16$2_0_OnStack_1))
                                                                                                                                                                                                 (_$2_13_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                                                                (let
                                                                                                                                                                                                   ((idxprom17$2_0_1 _$2_13_1))
                                                                                                                                                                                                   (let
                                                                                                                                                                                                      ((arrayidx18$2_0_1 (+ a$2_0_1 (* 4 idxprom17$2_0_1)))
                                                                                                                                                                                                       (arrayidx18$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                                                                      (let
                                                                                                                                                                                                         ((HEAP$2_4 (store_ HEAP$2_3 STACK$2_1 arrayidx18$2_0_1 arrayidx18$2_0_OnStack_1 _$2_12_1)))
                                                                                                                                                                                                         (let
                                                                                                                                                                                                            ((_$2_14_1 (select_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                                                                            (let
                                                                                                                                                                                                               ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                                                                                                                                               (let
                                                                                                                                                                                                                  ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                                                                                                                                                  (let
                                                                                                                                                                                                                     ((HEAP$2_6 HEAP$2_5))
                                                                                                                                                                                                                     (let
                                                                                                                                                                                                                        ((HEAP$1_6 HEAP$1_res_1)
                                                                                                                                                                                                                         (STACK$1_2 STACK$1_res_1)
                                                                                                                                                                                                                         (retval.0$1_0_1 call$1_0_1))
                                                                                                                                                                                                                        (let
                                                                                                                                                                                                                           ((result$1_1 retval.0$1_0_1)
                                                                                                                                                                                                                            (HEAP$1_res_2 HEAP$1_6)
                                                                                                                                                                                                                            (STACK$1_res_2 STACK$1_2)
                                                                                                                                                                                                                            (HEAP$2_7 HEAP$2_res_1)
                                                                                                                                                                                                                            (STACK$2_2 STACK$2_res_1)
                                                                                                                                                                                                                            (retval.0$2_0_1 call$2_0_1))
                                                                                                                                                                                                                           (let
                                                                                                                                                                                                                              ((result$2_1 retval.0$2_0_1)
                                                                                                                                                                                                                               (HEAP$2_res_2 HEAP$2_7)
                                                                                                                                                                                                                               (STACK$2_res_2 STACK$2_2))
                                                                                                                                                                                                                              (=>
                                                                                                                                                                                                                                 (and
                                                                                                                                                                                                                                    (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                                                                                                                                    cmp$1_0_1
                                                                                                                                                                                                                                    cmp4$1_0_1
                                                                                                                                                                                                                                    cmp$2_0_1
                                                                                                                                                                                                                                    cmp3$2_0_1
                                                                                                                                                                                                                                    (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_5 SP$1_1 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_6 SP$2_1 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1))
                                                                                                                                                                                                                                 (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_2 HEAP$2_res_2 STACK$1_res_2 STACK$2_res_2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_5_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((idx.ext6$1_0_1 _$1_5_1))
                                             (let
                                                ((add.ptr7$1_0_1 (+ a$1_0_1 (* 4 idx.ext6$1_0_1)))
                                                 (add.ptr7$1_0_OnStack_1 a$1_0_OnStack_1))
                                                (let
                                                   ((_$1_6_1 (select_ HEAP$1_1 STACK$1_1 add.ptr7$1_0_1 add.ptr7$1_0_OnStack_1))
                                                    (_$1_7_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                   (let
                                                      ((idx.ext8$1_0_1 _$1_7_1))
                                                      (let
                                                         ((add.ptr9$1_0_1 (+ a$1_0_1 (* 4 idx.ext8$1_0_1)))
                                                          (add.ptr9$1_0_OnStack_1 a$1_0_OnStack_1))
                                                         (let
                                                            ((add.ptr10$1_0_1 (+ add.ptr9$1_0_1 (* 4 1)))
                                                             (add.ptr10$1_0_OnStack_1 add.ptr9$1_0_OnStack_1))
                                                            (let
                                                               ((_$1_8_1 (select_ HEAP$1_1 STACK$1_1 add.ptr10$1_0_1 add.ptr10$1_0_OnStack_1))
                                                                (_$1_9_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                               (let
                                                                  ((idx.ext11$1_0_1 _$1_9_1))
                                                                  (let
                                                                     ((add.ptr12$1_0_1 (+ a$1_0_1 (* 4 idx.ext11$1_0_1)))
                                                                      (add.ptr12$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                     (let
                                                                        ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 add.ptr12$1_0_1 add.ptr12$1_0_OnStack_1 _$1_8_1)))
                                                                        (let
                                                                           ((_$1_10_1 (select_ HEAP$1_2 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                           (let
                                                                              ((idx.ext13$1_0_1 _$1_10_1))
                                                                              (let
                                                                                 ((add.ptr14$1_0_1 (+ a$1_0_1 (* 4 idx.ext13$1_0_1)))
                                                                                  (add.ptr14$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                                 (let
                                                                                    ((add.ptr15$1_0_1 (+ add.ptr14$1_0_1 (* 4 1)))
                                                                                     (add.ptr15$1_0_OnStack_1 add.ptr14$1_0_OnStack_1))
                                                                                    (let
                                                                                       ((HEAP$1_3 (store_ HEAP$1_2 STACK$1_1 add.ptr15$1_0_1 add.ptr15$1_0_OnStack_1 _$1_6_1)))
                                                                                       (let
                                                                                          ((_$1_11_1 (select_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                                          (let
                                                                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                                                                             (let
                                                                                                ((HEAP$1_4 (store_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                                                                (let
                                                                                                   ((HEAP$1_5 HEAP$1_4)
                                                                                                    (a$2_0_1 a$2_0_old_1)
                                                                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                                                                    (i$2_0_1 i$2_0_old_1)
                                                                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                                                                    (HEAP$2_1 HEAP$2_old_1)
                                                                                                    (SP$2_1 SP$2_old_1)
                                                                                                    (STACK$2_1 STACK$2_old_1))
                                                                                                   (let
                                                                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                      (let
                                                                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                                                                         (let
                                                                                                            ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                            (let
                                                                                                               ((idxprom$2_0_1 _$2_1_1))
                                                                                                               (let
                                                                                                                  ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                                                                                                   (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                  (let
                                                                                                                     ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                                                                                                      (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                     (let
                                                                                                                        ((add$2_0_1 (+ _$2_3_1 1)))
                                                                                                                        (let
                                                                                                                           ((idxprom1$2_0_1 add$2_0_1))
                                                                                                                           (let
                                                                                                                              ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                                                                                                               (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                              (let
                                                                                                                                 ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                                                                                                 (let
                                                                                                                                    ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                                                                                                    (let
                                                                                                                                       ((_$2_14_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                       (let
                                                                                                                                          ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                                                                          (let
                                                                                                                                             ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                                                                             (let
                                                                                                                                                ((HEAP$2_3 HEAP$2_2))
                                                                                                                                                (=>
                                                                                                                                                   (and
                                                                                                                                                      (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                                                      cmp$1_0_1
                                                                                                                                                      cmp4$1_0_1
                                                                                                                                                      cmp$2_0_1
                                                                                                                                                      (not cmp3$2_0_1))
                                                                                                                                                   (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_5 SP$1_1 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_3 SP$2_1 STACK$2_1))))))))))))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_5_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((idx.ext6$1_0_1 _$1_5_1))
                                             (let
                                                ((add.ptr7$1_0_1 (+ a$1_0_1 (* 4 idx.ext6$1_0_1)))
                                                 (add.ptr7$1_0_OnStack_1 a$1_0_OnStack_1))
                                                (let
                                                   ((_$1_6_1 (select_ HEAP$1_1 STACK$1_1 add.ptr7$1_0_1 add.ptr7$1_0_OnStack_1))
                                                    (_$1_7_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                   (let
                                                      ((idx.ext8$1_0_1 _$1_7_1))
                                                      (let
                                                         ((add.ptr9$1_0_1 (+ a$1_0_1 (* 4 idx.ext8$1_0_1)))
                                                          (add.ptr9$1_0_OnStack_1 a$1_0_OnStack_1))
                                                         (let
                                                            ((add.ptr10$1_0_1 (+ add.ptr9$1_0_1 (* 4 1)))
                                                             (add.ptr10$1_0_OnStack_1 add.ptr9$1_0_OnStack_1))
                                                            (let
                                                               ((_$1_8_1 (select_ HEAP$1_1 STACK$1_1 add.ptr10$1_0_1 add.ptr10$1_0_OnStack_1))
                                                                (_$1_9_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                               (let
                                                                  ((idx.ext11$1_0_1 _$1_9_1))
                                                                  (let
                                                                     ((add.ptr12$1_0_1 (+ a$1_0_1 (* 4 idx.ext11$1_0_1)))
                                                                      (add.ptr12$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                     (let
                                                                        ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 add.ptr12$1_0_1 add.ptr12$1_0_OnStack_1 _$1_8_1)))
                                                                        (let
                                                                           ((_$1_10_1 (select_ HEAP$1_2 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                           (let
                                                                              ((idx.ext13$1_0_1 _$1_10_1))
                                                                              (let
                                                                                 ((add.ptr14$1_0_1 (+ a$1_0_1 (* 4 idx.ext13$1_0_1)))
                                                                                  (add.ptr14$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                                 (let
                                                                                    ((add.ptr15$1_0_1 (+ add.ptr14$1_0_1 (* 4 1)))
                                                                                     (add.ptr15$1_0_OnStack_1 add.ptr14$1_0_OnStack_1))
                                                                                    (let
                                                                                       ((HEAP$1_3 (store_ HEAP$1_2 STACK$1_1 add.ptr15$1_0_1 add.ptr15$1_0_OnStack_1 _$1_6_1)))
                                                                                       (let
                                                                                          ((_$1_11_1 (select_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                                          (let
                                                                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                                                                             (let
                                                                                                ((HEAP$1_4 (store_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                                                                (let
                                                                                                   ((HEAP$1_5 HEAP$1_4)
                                                                                                    (a$2_0_1 a$2_0_old_1)
                                                                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                                                                    (i$2_0_1 i$2_0_old_1)
                                                                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                                                                    (HEAP$2_1 HEAP$2_old_1)
                                                                                                    (SP$2_1 SP$2_old_1)
                                                                                                    (STACK$2_1 STACK$2_old_1))
                                                                                                   (let
                                                                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                      (let
                                                                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                                                                         (let
                                                                                                            ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                            (let
                                                                                                               ((idxprom$2_0_1 _$2_1_1))
                                                                                                               (let
                                                                                                                  ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                                                                                                   (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                  (let
                                                                                                                     ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                                                                                                      (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                     (let
                                                                                                                        ((add$2_0_1 (+ _$2_3_1 1)))
                                                                                                                        (let
                                                                                                                           ((idxprom1$2_0_1 add$2_0_1))
                                                                                                                           (let
                                                                                                                              ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                                                                                                               (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                              (let
                                                                                                                                 ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                                                                                                 (let
                                                                                                                                    ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                                                                                                    (let
                                                                                                                                       ((_$2_14_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                       (let
                                                                                                                                          ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                                                                          (let
                                                                                                                                             ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                                                                             (let
                                                                                                                                                ((HEAP$2_3 HEAP$2_2))
                                                                                                                                                (let
                                                                                                                                                   ((HEAP$1_6 HEAP$1_res_1)
                                                                                                                                                    (STACK$1_2 STACK$1_res_1)
                                                                                                                                                    (retval.0$1_0_1 call$1_0_1))
                                                                                                                                                   (let
                                                                                                                                                      ((result$1_1 retval.0$1_0_1)
                                                                                                                                                       (HEAP$1_res_2 HEAP$1_6)
                                                                                                                                                       (STACK$1_res_2 STACK$1_2)
                                                                                                                                                       (HEAP$2_4 HEAP$2_res_1)
                                                                                                                                                       (STACK$2_2 STACK$2_res_1)
                                                                                                                                                       (retval.0$2_0_1 call$2_0_1))
                                                                                                                                                      (let
                                                                                                                                                         ((result$2_1 retval.0$2_0_1)
                                                                                                                                                          (HEAP$2_res_2 HEAP$2_4)
                                                                                                                                                          (STACK$2_res_2 STACK$2_2))
                                                                                                                                                         (=>
                                                                                                                                                            (and
                                                                                                                                                               (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                                                               cmp$1_0_1
                                                                                                                                                               cmp4$1_0_1
                                                                                                                                                               cmp$2_0_1
                                                                                                                                                               (not cmp3$2_0_1)
                                                                                                                                                               (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_5 SP$1_1 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_3 SP$2_1 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1))
                                                                                                                                                            (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_2 HEAP$2_res_2 STACK$1_res_2 STACK$2_res_2)))))))))))))))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_5_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((idx.ext6$1_0_1 _$1_5_1))
                                             (let
                                                ((add.ptr7$1_0_1 (+ a$1_0_1 (* 4 idx.ext6$1_0_1)))
                                                 (add.ptr7$1_0_OnStack_1 a$1_0_OnStack_1))
                                                (let
                                                   ((_$1_6_1 (select_ HEAP$1_1 STACK$1_1 add.ptr7$1_0_1 add.ptr7$1_0_OnStack_1))
                                                    (_$1_7_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                   (let
                                                      ((idx.ext8$1_0_1 _$1_7_1))
                                                      (let
                                                         ((add.ptr9$1_0_1 (+ a$1_0_1 (* 4 idx.ext8$1_0_1)))
                                                          (add.ptr9$1_0_OnStack_1 a$1_0_OnStack_1))
                                                         (let
                                                            ((add.ptr10$1_0_1 (+ add.ptr9$1_0_1 (* 4 1)))
                                                             (add.ptr10$1_0_OnStack_1 add.ptr9$1_0_OnStack_1))
                                                            (let
                                                               ((_$1_8_1 (select_ HEAP$1_1 STACK$1_1 add.ptr10$1_0_1 add.ptr10$1_0_OnStack_1))
                                                                (_$1_9_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                               (let
                                                                  ((idx.ext11$1_0_1 _$1_9_1))
                                                                  (let
                                                                     ((add.ptr12$1_0_1 (+ a$1_0_1 (* 4 idx.ext11$1_0_1)))
                                                                      (add.ptr12$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                     (let
                                                                        ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 add.ptr12$1_0_1 add.ptr12$1_0_OnStack_1 _$1_8_1)))
                                                                        (let
                                                                           ((_$1_10_1 (select_ HEAP$1_2 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                           (let
                                                                              ((idx.ext13$1_0_1 _$1_10_1))
                                                                              (let
                                                                                 ((add.ptr14$1_0_1 (+ a$1_0_1 (* 4 idx.ext13$1_0_1)))
                                                                                  (add.ptr14$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                                 (let
                                                                                    ((add.ptr15$1_0_1 (+ add.ptr14$1_0_1 (* 4 1)))
                                                                                     (add.ptr15$1_0_OnStack_1 add.ptr14$1_0_OnStack_1))
                                                                                    (let
                                                                                       ((HEAP$1_3 (store_ HEAP$1_2 STACK$1_1 add.ptr15$1_0_1 add.ptr15$1_0_OnStack_1 _$1_6_1)))
                                                                                       (let
                                                                                          ((_$1_11_1 (select_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                                          (let
                                                                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                                                                             (let
                                                                                                ((HEAP$1_4 (store_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                                                                (let
                                                                                                   ((HEAP$1_5 HEAP$1_4)
                                                                                                    (a$2_0_1 a$2_0_old_1)
                                                                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                                                                    (i$2_0_1 i$2_0_old_1)
                                                                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                                                                    (HEAP$2_1 HEAP$2_old_1)
                                                                                                    (SP$2_1 SP$2_old_1)
                                                                                                    (STACK$2_1 STACK$2_old_1))
                                                                                                   (let
                                                                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                      (let
                                                                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                                                                         (let
                                                                                                            ((retval.0$2_0_1 0))
                                                                                                            (let
                                                                                                               ((result$2_1 retval.0$2_0_1)
                                                                                                                (HEAP$2_res_1 HEAP$2_1)
                                                                                                                (STACK$2_res_1 STACK$2_1))
                                                                                                               (=>
                                                                                                                  (and
                                                                                                                     (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                     cmp$1_0_1
                                                                                                                     cmp4$1_0_1
                                                                                                                     (not cmp$2_0_1))
                                                                                                                  (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_5 SP$1_1 STACK$1_1)))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_5_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((idx.ext6$1_0_1 _$1_5_1))
                                             (let
                                                ((add.ptr7$1_0_1 (+ a$1_0_1 (* 4 idx.ext6$1_0_1)))
                                                 (add.ptr7$1_0_OnStack_1 a$1_0_OnStack_1))
                                                (let
                                                   ((_$1_6_1 (select_ HEAP$1_1 STACK$1_1 add.ptr7$1_0_1 add.ptr7$1_0_OnStack_1))
                                                    (_$1_7_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                   (let
                                                      ((idx.ext8$1_0_1 _$1_7_1))
                                                      (let
                                                         ((add.ptr9$1_0_1 (+ a$1_0_1 (* 4 idx.ext8$1_0_1)))
                                                          (add.ptr9$1_0_OnStack_1 a$1_0_OnStack_1))
                                                         (let
                                                            ((add.ptr10$1_0_1 (+ add.ptr9$1_0_1 (* 4 1)))
                                                             (add.ptr10$1_0_OnStack_1 add.ptr9$1_0_OnStack_1))
                                                            (let
                                                               ((_$1_8_1 (select_ HEAP$1_1 STACK$1_1 add.ptr10$1_0_1 add.ptr10$1_0_OnStack_1))
                                                                (_$1_9_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                               (let
                                                                  ((idx.ext11$1_0_1 _$1_9_1))
                                                                  (let
                                                                     ((add.ptr12$1_0_1 (+ a$1_0_1 (* 4 idx.ext11$1_0_1)))
                                                                      (add.ptr12$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                     (let
                                                                        ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 add.ptr12$1_0_1 add.ptr12$1_0_OnStack_1 _$1_8_1)))
                                                                        (let
                                                                           ((_$1_10_1 (select_ HEAP$1_2 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                           (let
                                                                              ((idx.ext13$1_0_1 _$1_10_1))
                                                                              (let
                                                                                 ((add.ptr14$1_0_1 (+ a$1_0_1 (* 4 idx.ext13$1_0_1)))
                                                                                  (add.ptr14$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                                 (let
                                                                                    ((add.ptr15$1_0_1 (+ add.ptr14$1_0_1 (* 4 1)))
                                                                                     (add.ptr15$1_0_OnStack_1 add.ptr14$1_0_OnStack_1))
                                                                                    (let
                                                                                       ((HEAP$1_3 (store_ HEAP$1_2 STACK$1_1 add.ptr15$1_0_1 add.ptr15$1_0_OnStack_1 _$1_6_1)))
                                                                                       (let
                                                                                          ((_$1_11_1 (select_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                                          (let
                                                                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                                                                             (let
                                                                                                ((HEAP$1_4 (store_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                                                                (let
                                                                                                   ((HEAP$1_5 HEAP$1_4)
                                                                                                    (a$2_0_1 a$2_0_old_1)
                                                                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                                                                    (i$2_0_1 i$2_0_old_1)
                                                                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                                                                    (HEAP$2_1 HEAP$2_old_1)
                                                                                                    (SP$2_1 SP$2_old_1)
                                                                                                    (STACK$2_1 STACK$2_old_1))
                                                                                                   (let
                                                                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                      (let
                                                                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                                                                         (let
                                                                                                            ((retval.0$2_0_1 0))
                                                                                                            (let
                                                                                                               ((result$2_1 retval.0$2_0_1)
                                                                                                                (HEAP$2_res_1 HEAP$2_1)
                                                                                                                (STACK$2_res_1 STACK$2_1))
                                                                                                               (let
                                                                                                                  ((HEAP$1_6 HEAP$1_res_1)
                                                                                                                   (STACK$1_2 STACK$1_res_1)
                                                                                                                   (retval.0$1_0_1 call$1_0_1))
                                                                                                                  (let
                                                                                                                     ((result$1_1 retval.0$1_0_1)
                                                                                                                      (HEAP$1_res_2 HEAP$1_6)
                                                                                                                      (STACK$1_res_2 STACK$1_2))
                                                                                                                     (=>
                                                                                                                        (and
                                                                                                                           (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                           cmp$1_0_1
                                                                                                                           cmp4$1_0_1
                                                                                                                           (not cmp$2_0_1)
                                                                                                                           (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_5 SP$1_1 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1))
                                                                                                                        (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_2 HEAP$2_res_1 STACK$1_res_2 STACK$2_res_1)))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_11_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                             (let
                                                ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                (let
                                                   ((HEAP$1_3 HEAP$1_2)
                                                    (a$2_0_1 a$2_0_old_1)
                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                    (i$2_0_1 i$2_0_old_1)
                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                    (HEAP$2_1 HEAP$2_old_1)
                                                    (SP$2_1 SP$2_old_1)
                                                    (STACK$2_1 STACK$2_old_1))
                                                   (let
                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                      (let
                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                         (let
                                                            ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                            (let
                                                               ((idxprom$2_0_1 _$2_1_1))
                                                               (let
                                                                  ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                                                   (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                  (let
                                                                     ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                                                      (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                     (let
                                                                        ((add$2_0_1 (+ _$2_3_1 1)))
                                                                        (let
                                                                           ((idxprom1$2_0_1 add$2_0_1))
                                                                           (let
                                                                              ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                                                               (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                              (let
                                                                                 ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                                                 (let
                                                                                    ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                                                    (let
                                                                                       ((_$2_5_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                       (let
                                                                                          ((idxprom5$2_0_1 _$2_5_1))
                                                                                          (let
                                                                                             ((arrayidx6$2_0_1 (+ a$2_0_1 (* 4 idxprom5$2_0_1)))
                                                                                              (arrayidx6$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                             (let
                                                                                                ((_$2_6_1 (select_ HEAP$2_1 STACK$2_1 arrayidx6$2_0_1 arrayidx6$2_0_OnStack_1))
                                                                                                 (_$2_7_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                (let
                                                                                                   ((add7$2_0_1 (+ _$2_7_1 1)))
                                                                                                   (let
                                                                                                      ((idxprom8$2_0_1 add7$2_0_1))
                                                                                                      (let
                                                                                                         ((arrayidx9$2_0_1 (+ a$2_0_1 (* 4 idxprom8$2_0_1)))
                                                                                                          (arrayidx9$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                         (let
                                                                                                            ((_$2_8_1 (select_ HEAP$2_1 STACK$2_1 arrayidx9$2_0_1 arrayidx9$2_0_OnStack_1))
                                                                                                             (_$2_9_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                            (let
                                                                                                               ((idxprom10$2_0_1 _$2_9_1))
                                                                                                               (let
                                                                                                                  ((arrayidx11$2_0_1 (+ a$2_0_1 (* 4 idxprom10$2_0_1)))
                                                                                                                   (arrayidx11$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                  (let
                                                                                                                     ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 arrayidx11$2_0_1 arrayidx11$2_0_OnStack_1 _$2_8_1)))
                                                                                                                     (let
                                                                                                                        ((_$2_10_1 (select_ HEAP$2_2 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                        (let
                                                                                                                           ((add12$2_0_1 (+ _$2_10_1 1)))
                                                                                                                           (let
                                                                                                                              ((idxprom13$2_0_1 add12$2_0_1))
                                                                                                                              (let
                                                                                                                                 ((arrayidx14$2_0_1 (+ a$2_0_1 (* 4 idxprom13$2_0_1)))
                                                                                                                                  (arrayidx14$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                 (let
                                                                                                                                    ((HEAP$2_3 (store_ HEAP$2_2 STACK$2_1 arrayidx14$2_0_1 arrayidx14$2_0_OnStack_1 _$2_6_1)))
                                                                                                                                    (let
                                                                                                                                       ((_$2_11_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                       (let
                                                                                                                                          ((idxprom15$2_0_1 _$2_11_1))
                                                                                                                                          (let
                                                                                                                                             ((arrayidx16$2_0_1 (+ a$2_0_1 (* 4 idxprom15$2_0_1)))
                                                                                                                                              (arrayidx16$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                             (let
                                                                                                                                                ((_$2_12_1 (select_ HEAP$2_3 STACK$2_1 arrayidx16$2_0_1 arrayidx16$2_0_OnStack_1))
                                                                                                                                                 (_$2_13_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                (let
                                                                                                                                                   ((idxprom17$2_0_1 _$2_13_1))
                                                                                                                                                   (let
                                                                                                                                                      ((arrayidx18$2_0_1 (+ a$2_0_1 (* 4 idxprom17$2_0_1)))
                                                                                                                                                       (arrayidx18$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                      (let
                                                                                                                                                         ((HEAP$2_4 (store_ HEAP$2_3 STACK$2_1 arrayidx18$2_0_1 arrayidx18$2_0_OnStack_1 _$2_12_1)))
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_14_1 (select_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                            (let
                                                                                                                                                               ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                                                                                               (let
                                                                                                                                                                  ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                                                                                                  (let
                                                                                                                                                                     ((HEAP$2_6 HEAP$2_5))
                                                                                                                                                                     (=>
                                                                                                                                                                        (and
                                                                                                                                                                           (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                                                                           cmp$1_0_1
                                                                                                                                                                           (not cmp4$1_0_1)
                                                                                                                                                                           cmp$2_0_1
                                                                                                                                                                           cmp3$2_0_1)
                                                                                                                                                                        (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_3 SP$1_1 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_6 SP$2_1 STACK$2_1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_11_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                             (let
                                                ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                (let
                                                   ((HEAP$1_3 HEAP$1_2)
                                                    (a$2_0_1 a$2_0_old_1)
                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                    (i$2_0_1 i$2_0_old_1)
                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                    (HEAP$2_1 HEAP$2_old_1)
                                                    (SP$2_1 SP$2_old_1)
                                                    (STACK$2_1 STACK$2_old_1))
                                                   (let
                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                      (let
                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                         (let
                                                            ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                            (let
                                                               ((idxprom$2_0_1 _$2_1_1))
                                                               (let
                                                                  ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                                                   (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                  (let
                                                                     ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                                                      (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                     (let
                                                                        ((add$2_0_1 (+ _$2_3_1 1)))
                                                                        (let
                                                                           ((idxprom1$2_0_1 add$2_0_1))
                                                                           (let
                                                                              ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                                                               (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                              (let
                                                                                 ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                                                 (let
                                                                                    ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                                                    (let
                                                                                       ((_$2_5_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                       (let
                                                                                          ((idxprom5$2_0_1 _$2_5_1))
                                                                                          (let
                                                                                             ((arrayidx6$2_0_1 (+ a$2_0_1 (* 4 idxprom5$2_0_1)))
                                                                                              (arrayidx6$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                             (let
                                                                                                ((_$2_6_1 (select_ HEAP$2_1 STACK$2_1 arrayidx6$2_0_1 arrayidx6$2_0_OnStack_1))
                                                                                                 (_$2_7_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                (let
                                                                                                   ((add7$2_0_1 (+ _$2_7_1 1)))
                                                                                                   (let
                                                                                                      ((idxprom8$2_0_1 add7$2_0_1))
                                                                                                      (let
                                                                                                         ((arrayidx9$2_0_1 (+ a$2_0_1 (* 4 idxprom8$2_0_1)))
                                                                                                          (arrayidx9$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                         (let
                                                                                                            ((_$2_8_1 (select_ HEAP$2_1 STACK$2_1 arrayidx9$2_0_1 arrayidx9$2_0_OnStack_1))
                                                                                                             (_$2_9_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                            (let
                                                                                                               ((idxprom10$2_0_1 _$2_9_1))
                                                                                                               (let
                                                                                                                  ((arrayidx11$2_0_1 (+ a$2_0_1 (* 4 idxprom10$2_0_1)))
                                                                                                                   (arrayidx11$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                  (let
                                                                                                                     ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 arrayidx11$2_0_1 arrayidx11$2_0_OnStack_1 _$2_8_1)))
                                                                                                                     (let
                                                                                                                        ((_$2_10_1 (select_ HEAP$2_2 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                        (let
                                                                                                                           ((add12$2_0_1 (+ _$2_10_1 1)))
                                                                                                                           (let
                                                                                                                              ((idxprom13$2_0_1 add12$2_0_1))
                                                                                                                              (let
                                                                                                                                 ((arrayidx14$2_0_1 (+ a$2_0_1 (* 4 idxprom13$2_0_1)))
                                                                                                                                  (arrayidx14$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                 (let
                                                                                                                                    ((HEAP$2_3 (store_ HEAP$2_2 STACK$2_1 arrayidx14$2_0_1 arrayidx14$2_0_OnStack_1 _$2_6_1)))
                                                                                                                                    (let
                                                                                                                                       ((_$2_11_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                       (let
                                                                                                                                          ((idxprom15$2_0_1 _$2_11_1))
                                                                                                                                          (let
                                                                                                                                             ((arrayidx16$2_0_1 (+ a$2_0_1 (* 4 idxprom15$2_0_1)))
                                                                                                                                              (arrayidx16$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                             (let
                                                                                                                                                ((_$2_12_1 (select_ HEAP$2_3 STACK$2_1 arrayidx16$2_0_1 arrayidx16$2_0_OnStack_1))
                                                                                                                                                 (_$2_13_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                (let
                                                                                                                                                   ((idxprom17$2_0_1 _$2_13_1))
                                                                                                                                                   (let
                                                                                                                                                      ((arrayidx18$2_0_1 (+ a$2_0_1 (* 4 idxprom17$2_0_1)))
                                                                                                                                                       (arrayidx18$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                                                      (let
                                                                                                                                                         ((HEAP$2_4 (store_ HEAP$2_3 STACK$2_1 arrayidx18$2_0_1 arrayidx18$2_0_OnStack_1 _$2_12_1)))
                                                                                                                                                         (let
                                                                                                                                                            ((_$2_14_1 (select_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                                                            (let
                                                                                                                                                               ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                                                                                               (let
                                                                                                                                                                  ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                                                                                                  (let
                                                                                                                                                                     ((HEAP$2_6 HEAP$2_5))
                                                                                                                                                                     (let
                                                                                                                                                                        ((HEAP$1_4 HEAP$1_res_1)
                                                                                                                                                                         (STACK$1_2 STACK$1_res_1)
                                                                                                                                                                         (retval.0$1_0_1 call$1_0_1))
                                                                                                                                                                        (let
                                                                                                                                                                           ((result$1_1 retval.0$1_0_1)
                                                                                                                                                                            (HEAP$1_res_2 HEAP$1_4)
                                                                                                                                                                            (STACK$1_res_2 STACK$1_2)
                                                                                                                                                                            (HEAP$2_7 HEAP$2_res_1)
                                                                                                                                                                            (STACK$2_2 STACK$2_res_1)
                                                                                                                                                                            (retval.0$2_0_1 call$2_0_1))
                                                                                                                                                                           (let
                                                                                                                                                                              ((result$2_1 retval.0$2_0_1)
                                                                                                                                                                               (HEAP$2_res_2 HEAP$2_7)
                                                                                                                                                                               (STACK$2_res_2 STACK$2_2))
                                                                                                                                                                              (=>
                                                                                                                                                                                 (and
                                                                                                                                                                                    (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                                                                                    cmp$1_0_1
                                                                                                                                                                                    (not cmp4$1_0_1)
                                                                                                                                                                                    cmp$2_0_1
                                                                                                                                                                                    cmp3$2_0_1
                                                                                                                                                                                    (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_3 SP$1_1 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_6 SP$2_1 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1))
                                                                                                                                                                                 (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_2 HEAP$2_res_2 STACK$1_res_2 STACK$2_res_2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_11_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                             (let
                                                ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                (let
                                                   ((HEAP$1_3 HEAP$1_2)
                                                    (a$2_0_1 a$2_0_old_1)
                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                    (i$2_0_1 i$2_0_old_1)
                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                    (HEAP$2_1 HEAP$2_old_1)
                                                    (SP$2_1 SP$2_old_1)
                                                    (STACK$2_1 STACK$2_old_1))
                                                   (let
                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                      (let
                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                         (let
                                                            ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                            (let
                                                               ((idxprom$2_0_1 _$2_1_1))
                                                               (let
                                                                  ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                                                   (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                  (let
                                                                     ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                                                      (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                     (let
                                                                        ((add$2_0_1 (+ _$2_3_1 1)))
                                                                        (let
                                                                           ((idxprom1$2_0_1 add$2_0_1))
                                                                           (let
                                                                              ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                                                               (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                              (let
                                                                                 ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                                                 (let
                                                                                    ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                                                    (let
                                                                                       ((_$2_14_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                       (let
                                                                                          ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                          (let
                                                                                             ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                             (let
                                                                                                ((HEAP$2_3 HEAP$2_2))
                                                                                                (=>
                                                                                                   (and
                                                                                                      (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                      cmp$1_0_1
                                                                                                      (not cmp4$1_0_1)
                                                                                                      cmp$2_0_1
                                                                                                      (not cmp3$2_0_1))
                                                                                                   (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_3 SP$1_1 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_3 SP$2_1 STACK$2_1))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_11_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                             (let
                                                ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                (let
                                                   ((HEAP$1_3 HEAP$1_2)
                                                    (a$2_0_1 a$2_0_old_1)
                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                    (i$2_0_1 i$2_0_old_1)
                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                    (HEAP$2_1 HEAP$2_old_1)
                                                    (SP$2_1 SP$2_old_1)
                                                    (STACK$2_1 STACK$2_old_1))
                                                   (let
                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                      (let
                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                         (let
                                                            ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                            (let
                                                               ((idxprom$2_0_1 _$2_1_1))
                                                               (let
                                                                  ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                                                   (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                  (let
                                                                     ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                                                      (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                     (let
                                                                        ((add$2_0_1 (+ _$2_3_1 1)))
                                                                        (let
                                                                           ((idxprom1$2_0_1 add$2_0_1))
                                                                           (let
                                                                              ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                                                               (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                              (let
                                                                                 ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                                                 (let
                                                                                    ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                                                    (let
                                                                                       ((_$2_14_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                       (let
                                                                                          ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                          (let
                                                                                             ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                             (let
                                                                                                ((HEAP$2_3 HEAP$2_2))
                                                                                                (let
                                                                                                   ((HEAP$1_4 HEAP$1_res_1)
                                                                                                    (STACK$1_2 STACK$1_res_1)
                                                                                                    (retval.0$1_0_1 call$1_0_1))
                                                                                                   (let
                                                                                                      ((result$1_1 retval.0$1_0_1)
                                                                                                       (HEAP$1_res_2 HEAP$1_4)
                                                                                                       (STACK$1_res_2 STACK$1_2)
                                                                                                       (HEAP$2_4 HEAP$2_res_1)
                                                                                                       (STACK$2_2 STACK$2_res_1)
                                                                                                       (retval.0$2_0_1 call$2_0_1))
                                                                                                      (let
                                                                                                         ((result$2_1 retval.0$2_0_1)
                                                                                                          (HEAP$2_res_2 HEAP$2_4)
                                                                                                          (STACK$2_res_2 STACK$2_2))
                                                                                                         (=>
                                                                                                            (and
                                                                                                               (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                               cmp$1_0_1
                                                                                                               (not cmp4$1_0_1)
                                                                                                               cmp$2_0_1
                                                                                                               (not cmp3$2_0_1)
                                                                                                               (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_3 SP$1_1 STACK$1_1 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_3 SP$2_1 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1))
                                                                                                            (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_2 HEAP$2_res_2 STACK$1_res_2 STACK$2_res_2)))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_11_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                             (let
                                                ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                (let
                                                   ((HEAP$1_3 HEAP$1_2)
                                                    (a$2_0_1 a$2_0_old_1)
                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                    (i$2_0_1 i$2_0_old_1)
                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                    (HEAP$2_1 HEAP$2_old_1)
                                                    (SP$2_1 SP$2_old_1)
                                                    (STACK$2_1 STACK$2_old_1))
                                                   (let
                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                      (let
                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                         (let
                                                            ((retval.0$2_0_1 0))
                                                            (let
                                                               ((result$2_1 retval.0$2_0_1)
                                                                (HEAP$2_res_1 HEAP$2_1)
                                                                (STACK$2_res_1 STACK$2_1))
                                                               (=>
                                                                  (and
                                                                     (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                     cmp$1_0_1
                                                                     (not cmp4$1_0_1)
                                                                     (not cmp$2_0_1))
                                                                  (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_3 SP$1_1 STACK$1_1)))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_11_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                             (let
                                                ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                (let
                                                   ((HEAP$1_3 HEAP$1_2)
                                                    (a$2_0_1 a$2_0_old_1)
                                                    (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                                                    (i$2_0_1 i$2_0_old_1)
                                                    (rvp_j$2_0_1 rvp_j$2_0_old_1)
                                                    (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                                                    (HEAP$2_1 HEAP$2_old_1)
                                                    (SP$2_1 SP$2_old_1)
                                                    (STACK$2_1 STACK$2_old_1))
                                                   (let
                                                      ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                      (let
                                                         ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                                                         (let
                                                            ((retval.0$2_0_1 0))
                                                            (let
                                                               ((result$2_1 retval.0$2_0_1)
                                                                (HEAP$2_res_1 HEAP$2_1)
                                                                (STACK$2_res_1 STACK$2_1))
                                                               (let
                                                                  ((HEAP$1_4 HEAP$1_res_1)
                                                                   (STACK$1_2 STACK$1_res_1)
                                                                   (retval.0$1_0_1 call$1_0_1))
                                                                  (let
                                                                     ((result$1_1 retval.0$1_0_1)
                                                                      (HEAP$1_res_2 HEAP$1_4)
                                                                      (STACK$1_res_2 STACK$1_2))
                                                                     (=>
                                                                        (and
                                                                           (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                           cmp$1_0_1
                                                                           (not cmp4$1_0_1)
                                                                           (not cmp$2_0_1)
                                                                           (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_3 SP$1_1 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1))
                                                                        (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_2 HEAP$2_res_1 STACK$1_res_2 STACK$2_res_1)))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (i$2_0_1 i$2_0_old_1)
                   (rvp_j$2_0_1 rvp_j$2_0_old_1)
                   (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1)
                   (STACK$2_1 STACK$2_old_1))
                  (let
                     ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                     (let
                        ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                        (let
                           ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                           (let
                              ((idxprom$2_0_1 _$2_1_1))
                              (let
                                 ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                  (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                 (let
                                    ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                     (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                    (let
                                       ((add$2_0_1 (+ _$2_3_1 1)))
                                       (let
                                          ((idxprom1$2_0_1 add$2_0_1))
                                          (let
                                             ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                              (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                             (let
                                                ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                (let
                                                   ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                   (let
                                                      ((_$2_5_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                      (let
                                                         ((idxprom5$2_0_1 _$2_5_1))
                                                         (let
                                                            ((arrayidx6$2_0_1 (+ a$2_0_1 (* 4 idxprom5$2_0_1)))
                                                             (arrayidx6$2_0_OnStack_1 a$2_0_OnStack_1))
                                                            (let
                                                               ((_$2_6_1 (select_ HEAP$2_1 STACK$2_1 arrayidx6$2_0_1 arrayidx6$2_0_OnStack_1))
                                                                (_$2_7_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                               (let
                                                                  ((add7$2_0_1 (+ _$2_7_1 1)))
                                                                  (let
                                                                     ((idxprom8$2_0_1 add7$2_0_1))
                                                                     (let
                                                                        ((arrayidx9$2_0_1 (+ a$2_0_1 (* 4 idxprom8$2_0_1)))
                                                                         (arrayidx9$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                        (let
                                                                           ((_$2_8_1 (select_ HEAP$2_1 STACK$2_1 arrayidx9$2_0_1 arrayidx9$2_0_OnStack_1))
                                                                            (_$2_9_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                           (let
                                                                              ((idxprom10$2_0_1 _$2_9_1))
                                                                              (let
                                                                                 ((arrayidx11$2_0_1 (+ a$2_0_1 (* 4 idxprom10$2_0_1)))
                                                                                  (arrayidx11$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                 (let
                                                                                    ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 arrayidx11$2_0_1 arrayidx11$2_0_OnStack_1 _$2_8_1)))
                                                                                    (let
                                                                                       ((_$2_10_1 (select_ HEAP$2_2 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                       (let
                                                                                          ((add12$2_0_1 (+ _$2_10_1 1)))
                                                                                          (let
                                                                                             ((idxprom13$2_0_1 add12$2_0_1))
                                                                                             (let
                                                                                                ((arrayidx14$2_0_1 (+ a$2_0_1 (* 4 idxprom13$2_0_1)))
                                                                                                 (arrayidx14$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                (let
                                                                                                   ((HEAP$2_3 (store_ HEAP$2_2 STACK$2_1 arrayidx14$2_0_1 arrayidx14$2_0_OnStack_1 _$2_6_1)))
                                                                                                   (let
                                                                                                      ((_$2_11_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                      (let
                                                                                                         ((idxprom15$2_0_1 _$2_11_1))
                                                                                                         (let
                                                                                                            ((arrayidx16$2_0_1 (+ a$2_0_1 (* 4 idxprom15$2_0_1)))
                                                                                                             (arrayidx16$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                            (let
                                                                                                               ((_$2_12_1 (select_ HEAP$2_3 STACK$2_1 arrayidx16$2_0_1 arrayidx16$2_0_OnStack_1))
                                                                                                                (_$2_13_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                               (let
                                                                                                                  ((idxprom17$2_0_1 _$2_13_1))
                                                                                                                  (let
                                                                                                                     ((arrayidx18$2_0_1 (+ a$2_0_1 (* 4 idxprom17$2_0_1)))
                                                                                                                      (arrayidx18$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                     (let
                                                                                                                        ((HEAP$2_4 (store_ HEAP$2_3 STACK$2_1 arrayidx18$2_0_1 arrayidx18$2_0_OnStack_1 _$2_12_1)))
                                                                                                                        (let
                                                                                                                           ((_$2_14_1 (select_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                           (let
                                                                                                                              ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                                                              (let
                                                                                                                                 ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                                                                 (let
                                                                                                                                    ((HEAP$2_6 HEAP$2_5))
                                                                                                                                    (=>
                                                                                                                                       (and
                                                                                                                                          (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                                          (not cmp$1_0_1)
                                                                                                                                          cmp$2_0_1
                                                                                                                                          cmp3$2_0_1)
                                                                                                                                       (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_6 SP$2_1 STACK$2_1))))))))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (i$2_0_1 i$2_0_old_1)
                   (rvp_j$2_0_1 rvp_j$2_0_old_1)
                   (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1)
                   (STACK$2_1 STACK$2_old_1))
                  (let
                     ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                     (let
                        ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                        (let
                           ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                           (let
                              ((idxprom$2_0_1 _$2_1_1))
                              (let
                                 ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                  (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                 (let
                                    ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                     (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                    (let
                                       ((add$2_0_1 (+ _$2_3_1 1)))
                                       (let
                                          ((idxprom1$2_0_1 add$2_0_1))
                                          (let
                                             ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                              (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                             (let
                                                ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                (let
                                                   ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                   (let
                                                      ((_$2_5_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                      (let
                                                         ((idxprom5$2_0_1 _$2_5_1))
                                                         (let
                                                            ((arrayidx6$2_0_1 (+ a$2_0_1 (* 4 idxprom5$2_0_1)))
                                                             (arrayidx6$2_0_OnStack_1 a$2_0_OnStack_1))
                                                            (let
                                                               ((_$2_6_1 (select_ HEAP$2_1 STACK$2_1 arrayidx6$2_0_1 arrayidx6$2_0_OnStack_1))
                                                                (_$2_7_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                               (let
                                                                  ((add7$2_0_1 (+ _$2_7_1 1)))
                                                                  (let
                                                                     ((idxprom8$2_0_1 add7$2_0_1))
                                                                     (let
                                                                        ((arrayidx9$2_0_1 (+ a$2_0_1 (* 4 idxprom8$2_0_1)))
                                                                         (arrayidx9$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                        (let
                                                                           ((_$2_8_1 (select_ HEAP$2_1 STACK$2_1 arrayidx9$2_0_1 arrayidx9$2_0_OnStack_1))
                                                                            (_$2_9_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                           (let
                                                                              ((idxprom10$2_0_1 _$2_9_1))
                                                                              (let
                                                                                 ((arrayidx11$2_0_1 (+ a$2_0_1 (* 4 idxprom10$2_0_1)))
                                                                                  (arrayidx11$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                 (let
                                                                                    ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 arrayidx11$2_0_1 arrayidx11$2_0_OnStack_1 _$2_8_1)))
                                                                                    (let
                                                                                       ((_$2_10_1 (select_ HEAP$2_2 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                       (let
                                                                                          ((add12$2_0_1 (+ _$2_10_1 1)))
                                                                                          (let
                                                                                             ((idxprom13$2_0_1 add12$2_0_1))
                                                                                             (let
                                                                                                ((arrayidx14$2_0_1 (+ a$2_0_1 (* 4 idxprom13$2_0_1)))
                                                                                                 (arrayidx14$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                (let
                                                                                                   ((HEAP$2_3 (store_ HEAP$2_2 STACK$2_1 arrayidx14$2_0_1 arrayidx14$2_0_OnStack_1 _$2_6_1)))
                                                                                                   (let
                                                                                                      ((_$2_11_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                      (let
                                                                                                         ((idxprom15$2_0_1 _$2_11_1))
                                                                                                         (let
                                                                                                            ((arrayidx16$2_0_1 (+ a$2_0_1 (* 4 idxprom15$2_0_1)))
                                                                                                             (arrayidx16$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                            (let
                                                                                                               ((_$2_12_1 (select_ HEAP$2_3 STACK$2_1 arrayidx16$2_0_1 arrayidx16$2_0_OnStack_1))
                                                                                                                (_$2_13_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                               (let
                                                                                                                  ((idxprom17$2_0_1 _$2_13_1))
                                                                                                                  (let
                                                                                                                     ((arrayidx18$2_0_1 (+ a$2_0_1 (* 4 idxprom17$2_0_1)))
                                                                                                                      (arrayidx18$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                                     (let
                                                                                                                        ((HEAP$2_4 (store_ HEAP$2_3 STACK$2_1 arrayidx18$2_0_1 arrayidx18$2_0_OnStack_1 _$2_12_1)))
                                                                                                                        (let
                                                                                                                           ((_$2_14_1 (select_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                                           (let
                                                                                                                              ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                                                              (let
                                                                                                                                 ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                                                                 (let
                                                                                                                                    ((HEAP$2_6 HEAP$2_5))
                                                                                                                                    (let
                                                                                                                                       ((HEAP$2_7 HEAP$2_res_1)
                                                                                                                                        (STACK$2_2 STACK$2_res_1)
                                                                                                                                        (retval.0$2_0_1 call$2_0_1))
                                                                                                                                       (let
                                                                                                                                          ((result$2_1 retval.0$2_0_1)
                                                                                                                                           (HEAP$2_res_2 HEAP$2_7)
                                                                                                                                           (STACK$2_res_2 STACK$2_2))
                                                                                                                                          (=>
                                                                                                                                             (and
                                                                                                                                                (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                                                (not cmp$1_0_1)
                                                                                                                                                cmp$2_0_1
                                                                                                                                                cmp3$2_0_1
                                                                                                                                                (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_6 SP$2_1 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1))
                                                                                                                                             (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_1 HEAP$2_res_2 STACK$1_res_1 STACK$2_res_2))))))))))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (i$2_0_1 i$2_0_old_1)
                   (rvp_j$2_0_1 rvp_j$2_0_old_1)
                   (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1)
                   (STACK$2_1 STACK$2_old_1))
                  (let
                     ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                     (let
                        ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                        (let
                           ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                           (let
                              ((idxprom$2_0_1 _$2_1_1))
                              (let
                                 ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                  (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                 (let
                                    ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                     (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                    (let
                                       ((add$2_0_1 (+ _$2_3_1 1)))
                                       (let
                                          ((idxprom1$2_0_1 add$2_0_1))
                                          (let
                                             ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                              (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                             (let
                                                ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                (let
                                                   ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                   (let
                                                      ((_$2_14_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                      (let
                                                         ((inc$2_0_1 (+ _$2_14_1 1)))
                                                         (let
                                                            ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                            (let
                                                               ((HEAP$2_3 HEAP$2_2))
                                                               (=>
                                                                  (and
                                                                     (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                     (not cmp$1_0_1)
                                                                     cmp$2_0_1
                                                                     (not cmp3$2_0_1))
                                                                  (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_3 SP$2_1 STACK$2_1)))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (i$2_0_1 i$2_0_old_1)
                   (rvp_j$2_0_1 rvp_j$2_0_old_1)
                   (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1)
                   (STACK$2_1 STACK$2_old_1))
                  (let
                     ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                     (let
                        ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                        (let
                           ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                           (let
                              ((idxprom$2_0_1 _$2_1_1))
                              (let
                                 ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                                  (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                                 (let
                                    ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                                     (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                    (let
                                       ((add$2_0_1 (+ _$2_3_1 1)))
                                       (let
                                          ((idxprom1$2_0_1 add$2_0_1))
                                          (let
                                             ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                              (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                             (let
                                                ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                                (let
                                                   ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                                   (let
                                                      ((_$2_14_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                      (let
                                                         ((inc$2_0_1 (+ _$2_14_1 1)))
                                                         (let
                                                            ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                            (let
                                                               ((HEAP$2_3 HEAP$2_2))
                                                               (let
                                                                  ((HEAP$2_4 HEAP$2_res_1)
                                                                   (STACK$2_2 STACK$2_res_1)
                                                                   (retval.0$2_0_1 call$2_0_1))
                                                                  (let
                                                                     ((result$2_1 retval.0$2_0_1)
                                                                      (HEAP$2_res_2 HEAP$2_4)
                                                                      (STACK$2_res_2 STACK$2_2))
                                                                     (=>
                                                                        (and
                                                                           (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                           (not cmp$1_0_1)
                                                                           cmp$2_0_1
                                                                           (not cmp3$2_0_1)
                                                                           (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_3 SP$2_1 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1))
                                                                        (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_1 HEAP$2_res_2 STACK$1_res_1 STACK$2_res_2)))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (i$2_0_1 i$2_0_old_1)
                   (rvp_j$2_0_1 rvp_j$2_0_old_1)
                   (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1)
                   (STACK$2_1 STACK$2_old_1))
                  (let
                     ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                     (let
                        ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
                        (let
                           ((retval.0$2_0_1 0))
                           (let
                              ((result$2_1 retval.0$2_0_1)
                               (HEAP$2_res_1 HEAP$2_1)
                               (STACK$2_res_1 STACK$2_1))
                              (=>
                                 (and
                                    (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                    (not cmp$1_0_1)
                                    (not cmp$2_0_1))
                                 (INV_REC_Loop_bubble_sort_for1_for1^Loop_bubble_sort_for1_for1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1))
                (HEAP$1_2 HEAP$1_1)
                (a$2_0_1 a$2_0_old_1)
                (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                (n$2_0_1 n$2_0_old_1)
                (rvp_i$2_0_1 rvp_i$2_0_old_1)
                (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                (rvp_j$2_0_1 rvp_j$2_0_old_1)
                (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
                (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
                (HEAP$2_1 HEAP$2_old_1)
                (SP$2_1 SP$2_old_1)
                (STACK$2_1 STACK$2_old_1))
               (let
                  ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                  (let
                     ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
                     (let
                        ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1))
                         (HEAP$2_2 HEAP$2_1))
                        (let
                           ((HEAP$1_3 HEAP$1_res_1)
                            (STACK$1_2 STACK$1_res_1)
                            (idx.ext$1_0_1 call$1_0_1))
                           (let
                              ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                               (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1)
                               (HEAP$1_4 HEAP$1_3)
                               (HEAP$2_3 HEAP$2_res_1)
                               (STACK$2_2 STACK$2_res_1)
                               (idx.ext$2_0_1 call$2_0_1))
                              (let
                                 ((add.ptr$2_0_1 (+ a$2_0_1 (* 4 idx.ext$2_0_1)))
                                  (add.ptr$2_0_OnStack_1 a$2_0_OnStack_1)
                                  (HEAP$2_4 HEAP$2_3))
                                 (=>
                                    (and
                                       (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                       cmp$1_0_1
                                       cmp$2_0_1
                                       (INV_REC_rv_mult_int__int_^rv_mult_int__int_ 5 _$1_1_1 HEAP$1_2 SP$1_1 STACK$1_1 5 _$2_1_1 HEAP$2_2 SP$2_1 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1))
                                    (INV_REC_bubble_sort^bubble_sort_PRE add.ptr$1_0_1 add.ptr$1_0_OnStack_1 5 HEAP$1_4 SP$1_1 STACK$1_2 add.ptr$2_0_1 add.ptr$2_0_OnStack_1 5 HEAP$2_4 SP$2_1 STACK$2_2)))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1))
                (HEAP$1_2 HEAP$1_1)
                (a$2_0_1 a$2_0_old_1)
                (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                (n$2_0_1 n$2_0_old_1)
                (rvp_i$2_0_1 rvp_i$2_0_old_1)
                (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                (rvp_j$2_0_1 rvp_j$2_0_old_1)
                (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
                (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
                (HEAP$2_1 HEAP$2_old_1)
                (SP$2_1 SP$2_old_1)
                (STACK$2_1 STACK$2_old_1))
               (let
                  ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                  (let
                     ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
                     (let
                        ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1))
                         (HEAP$2_2 HEAP$2_1))
                        (let
                           ((HEAP$1_3 HEAP$1_res_1)
                            (STACK$1_2 STACK$1_res_1)
                            (idx.ext$1_0_1 call$1_0_1))
                           (let
                              ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                               (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1)
                               (HEAP$1_4 HEAP$1_3)
                               (HEAP$2_3 HEAP$2_res_1)
                               (STACK$2_2 STACK$2_res_1)
                               (idx.ext$2_0_1 call$2_0_1))
                              (let
                                 ((add.ptr$2_0_1 (+ a$2_0_1 (* 4 idx.ext$2_0_1)))
                                  (add.ptr$2_0_OnStack_1 a$2_0_OnStack_1)
                                  (HEAP$2_4 HEAP$2_3))
                                 (let
                                    ((HEAP$1_5 HEAP$1_res_2)
                                     (STACK$1_3 STACK$1_res_2))
                                    (let
                                       ((_$1_2_1 (select_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                                       (let
                                          ((sub$1_0_1 (- _$1_2_1 1)))
                                          (let
                                             ((HEAP$1_6 (store_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                             (let
                                                ((_$1_3_1 (select_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                (let
                                                   ((inc$1_0_1 (+ _$1_3_1 1)))
                                                   (let
                                                      ((HEAP$1_7 (store_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 inc$1_0_1)))
                                                      (let
                                                         ((HEAP$1_8 HEAP$1_7)
                                                          (HEAP$2_5 HEAP$2_res_2)
                                                          (STACK$2_3 STACK$2_res_2))
                                                         (let
                                                            ((_$2_2_1 (select_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                                                            (let
                                                               ((inc$2_0_1 (+ _$2_2_1 1)))
                                                               (let
                                                                  ((HEAP$2_6 (store_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 inc$2_0_1)))
                                                                  (let
                                                                     ((_$2_3_1 (select_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                     (let
                                                                        ((inc1$2_0_1 (+ _$2_3_1 1)))
                                                                        (let
                                                                           ((HEAP$2_7 (store_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc1$2_0_1)))
                                                                           (let
                                                                              ((HEAP$2_8 HEAP$2_7))
                                                                              (=>
                                                                                 (and
                                                                                    (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                    cmp$1_0_1
                                                                                    cmp$2_0_1
                                                                                    (INV_REC_rv_mult_int__int_^rv_mult_int__int_ 5 _$1_1_1 HEAP$1_2 SP$1_1 STACK$1_1 5 _$2_1_1 HEAP$2_2 SP$2_1 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1)
                                                                                    (INV_REC_bubble_sort^bubble_sort add.ptr$1_0_1 add.ptr$1_0_OnStack_1 5 HEAP$1_4 SP$1_1 STACK$1_2 add.ptr$2_0_1 add.ptr$2_0_OnStack_1 5 HEAP$2_4 SP$2_1 STACK$2_2 res1_1 res2_1 HEAP$1_res_2 HEAP$2_res_2 STACK$1_res_2 STACK$2_res_2))
                                                                                 (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 rvp_rvretval$1_0_1 rvp_rvretval$1_0_OnStack_1 HEAP$1_8 SP$1_1 STACK$1_3 a$2_0_1 a$2_0_OnStack_1 n$2_0_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 rvp_rvretval$2_0_1 rvp_rvretval$2_0_OnStack_1 HEAP$2_8 SP$2_1 STACK$2_3))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1))
                (HEAP$1_2 HEAP$1_1)
                (a$2_0_1 a$2_0_old_1)
                (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                (n$2_0_1 n$2_0_old_1)
                (rvp_i$2_0_1 rvp_i$2_0_old_1)
                (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                (rvp_j$2_0_1 rvp_j$2_0_old_1)
                (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
                (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
                (HEAP$2_1 HEAP$2_old_1)
                (SP$2_1 SP$2_old_1)
                (STACK$2_1 STACK$2_old_1))
               (let
                  ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                  (let
                     ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
                     (let
                        ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1))
                         (HEAP$2_2 HEAP$2_1))
                        (let
                           ((HEAP$1_3 HEAP$1_res_1)
                            (STACK$1_2 STACK$1_res_1)
                            (idx.ext$1_0_1 call$1_0_1))
                           (let
                              ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                               (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1)
                               (HEAP$1_4 HEAP$1_3)
                               (HEAP$2_3 HEAP$2_res_1)
                               (STACK$2_2 STACK$2_res_1)
                               (idx.ext$2_0_1 call$2_0_1))
                              (let
                                 ((add.ptr$2_0_1 (+ a$2_0_1 (* 4 idx.ext$2_0_1)))
                                  (add.ptr$2_0_OnStack_1 a$2_0_OnStack_1)
                                  (HEAP$2_4 HEAP$2_3))
                                 (let
                                    ((HEAP$1_5 HEAP$1_res_2)
                                     (STACK$1_3 STACK$1_res_2))
                                    (let
                                       ((_$1_2_1 (select_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                                       (let
                                          ((sub$1_0_1 (- _$1_2_1 1)))
                                          (let
                                             ((HEAP$1_6 (store_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                             (let
                                                ((_$1_3_1 (select_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                (let
                                                   ((inc$1_0_1 (+ _$1_3_1 1)))
                                                   (let
                                                      ((HEAP$1_7 (store_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 inc$1_0_1)))
                                                      (let
                                                         ((HEAP$1_8 HEAP$1_7)
                                                          (HEAP$2_5 HEAP$2_res_2)
                                                          (STACK$2_3 STACK$2_res_2))
                                                         (let
                                                            ((_$2_2_1 (select_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                                                            (let
                                                               ((inc$2_0_1 (+ _$2_2_1 1)))
                                                               (let
                                                                  ((HEAP$2_6 (store_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 inc$2_0_1)))
                                                                  (let
                                                                     ((_$2_3_1 (select_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                     (let
                                                                        ((inc1$2_0_1 (+ _$2_3_1 1)))
                                                                        (let
                                                                           ((HEAP$2_7 (store_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc1$2_0_1)))
                                                                           (let
                                                                              ((HEAP$2_8 HEAP$2_7))
                                                                              (let
                                                                                 ((HEAP$1_9 HEAP$1_res_3)
                                                                                  (STACK$1_4 STACK$1_res_3)
                                                                                  (retval.0$1_0_1 call1$1_0_1))
                                                                                 (let
                                                                                    ((result$1_1 retval.0$1_0_1)
                                                                                     (HEAP$1_res_4 HEAP$1_9)
                                                                                     (STACK$1_res_4 STACK$1_4)
                                                                                     (HEAP$2_9 HEAP$2_res_3)
                                                                                     (STACK$2_4 STACK$2_res_3)
                                                                                     (retval.0$2_0_1 call2$2_0_1))
                                                                                    (let
                                                                                       ((result$2_1 retval.0$2_0_1)
                                                                                        (HEAP$2_res_4 HEAP$2_9)
                                                                                        (STACK$2_res_4 STACK$2_4))
                                                                                       (=>
                                                                                          (and
                                                                                             (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                             cmp$1_0_1
                                                                                             cmp$2_0_1
                                                                                             (INV_REC_rv_mult_int__int_^rv_mult_int__int_ 5 _$1_1_1 HEAP$1_2 SP$1_1 STACK$1_1 5 _$2_1_1 HEAP$2_2 SP$2_1 STACK$2_1 call$1_0_1 call$2_0_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1)
                                                                                             (INV_REC_bubble_sort^bubble_sort add.ptr$1_0_1 add.ptr$1_0_OnStack_1 5 HEAP$1_4 SP$1_1 STACK$1_2 add.ptr$2_0_1 add.ptr$2_0_OnStack_1 5 HEAP$2_4 SP$2_1 STACK$2_2 res1_1 res2_1 HEAP$1_res_2 HEAP$2_res_2 STACK$1_res_2 STACK$2_res_2)
                                                                                             (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1 a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 rvp_rvretval$1_0_1 rvp_rvretval$1_0_OnStack_1 HEAP$1_8 SP$1_1 STACK$1_3 a$2_0_1 a$2_0_OnStack_1 n$2_0_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 rvp_rvretval$2_0_1 rvp_rvretval$2_0_OnStack_1 HEAP$2_8 SP$2_1 STACK$2_3 call1$1_0_1 call2$2_0_1 HEAP$1_res_3 HEAP$2_res_3 STACK$1_res_3 STACK$2_res_3))
                                                                                          (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_4 HEAP$2_res_4 STACK$1_res_4 STACK$2_res_4)))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1))
                (HEAP$1_2 HEAP$1_1)
                (a$2_0_1 a$2_0_old_1)
                (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                (n$2_0_1 n$2_0_old_1)
                (rvp_i$2_0_1 rvp_i$2_0_old_1)
                (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                (rvp_j$2_0_1 rvp_j$2_0_old_1)
                (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
                (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
                (HEAP$2_1 HEAP$2_old_1)
                (SP$2_1 SP$2_old_1)
                (STACK$2_1 STACK$2_old_1))
               (let
                  ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                  (let
                     ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
                     (let
                        ((retval.0$2_0_1 0))
                        (let
                           ((result$2_1 retval.0$2_0_1)
                            (HEAP$2_res_1 HEAP$2_1)
                            (STACK$2_res_1 STACK$2_1))
                           (let
                              ((HEAP$1_3 HEAP$1_res_1)
                               (STACK$1_2 STACK$1_res_1)
                               (idx.ext$1_0_1 call$1_0_1))
                              (let
                                 ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                                  (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1)
                                  (HEAP$1_4 HEAP$1_3))
                                 (=>
                                    (and
                                       (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                       cmp$1_0_1
                                       (not cmp$2_0_1)
                                       (INV_REC_rv_mult_int__int___1 5 _$1_1_1 HEAP$1_2 SP$1_1 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1))
                                    (INV_REC_bubble_sort__1_PRE add.ptr$1_0_1 add.ptr$1_0_OnStack_1 5 HEAP$1_4 SP$1_1 STACK$1_2)))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1))
                (HEAP$1_2 HEAP$1_1)
                (a$2_0_1 a$2_0_old_1)
                (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                (n$2_0_1 n$2_0_old_1)
                (rvp_i$2_0_1 rvp_i$2_0_old_1)
                (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                (rvp_j$2_0_1 rvp_j$2_0_old_1)
                (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
                (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
                (HEAP$2_1 HEAP$2_old_1)
                (SP$2_1 SP$2_old_1)
                (STACK$2_1 STACK$2_old_1))
               (let
                  ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                  (let
                     ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
                     (let
                        ((retval.0$2_0_1 0))
                        (let
                           ((result$2_1 retval.0$2_0_1)
                            (HEAP$2_res_1 HEAP$2_1)
                            (STACK$2_res_1 STACK$2_1))
                           (let
                              ((HEAP$1_3 HEAP$1_res_1)
                               (STACK$1_2 STACK$1_res_1)
                               (idx.ext$1_0_1 call$1_0_1))
                              (let
                                 ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                                  (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1)
                                  (HEAP$1_4 HEAP$1_3))
                                 (let
                                    ((HEAP$1_5 HEAP$1_res_2)
                                     (STACK$1_3 STACK$1_res_2))
                                    (let
                                       ((_$1_2_1 (select_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                                       (let
                                          ((sub$1_0_1 (- _$1_2_1 1)))
                                          (let
                                             ((HEAP$1_6 (store_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                             (let
                                                ((_$1_3_1 (select_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                (let
                                                   ((inc$1_0_1 (+ _$1_3_1 1)))
                                                   (let
                                                      ((HEAP$1_7 (store_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 inc$1_0_1)))
                                                      (let
                                                         ((HEAP$1_8 HEAP$1_7))
                                                         (=>
                                                            (and
                                                               (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                               cmp$1_0_1
                                                               (not cmp$2_0_1)
                                                               (INV_REC_rv_mult_int__int___1 5 _$1_1_1 HEAP$1_2 SP$1_1 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1)
                                                               (INV_REC_bubble_sort__1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1 5 HEAP$1_4 SP$1_1 STACK$1_2 res1_1 HEAP$1_res_2 STACK$1_res_2))
                                                            (INV_REC_Loop_foo_function_while1__1_PRE a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 rvp_rvretval$1_0_1 rvp_rvretval$1_0_OnStack_1 HEAP$1_8 SP$1_1 STACK$1_3)))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1))
                (HEAP$1_2 HEAP$1_1)
                (a$2_0_1 a$2_0_old_1)
                (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                (n$2_0_1 n$2_0_old_1)
                (rvp_i$2_0_1 rvp_i$2_0_old_1)
                (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                (rvp_j$2_0_1 rvp_j$2_0_old_1)
                (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
                (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
                (HEAP$2_1 HEAP$2_old_1)
                (SP$2_1 SP$2_old_1)
                (STACK$2_1 STACK$2_old_1))
               (let
                  ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                  (let
                     ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
                     (let
                        ((retval.0$2_0_1 0))
                        (let
                           ((result$2_1 retval.0$2_0_1)
                            (HEAP$2_res_1 HEAP$2_1)
                            (STACK$2_res_1 STACK$2_1))
                           (let
                              ((HEAP$1_3 HEAP$1_res_1)
                               (STACK$1_2 STACK$1_res_1)
                               (idx.ext$1_0_1 call$1_0_1))
                              (let
                                 ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                                  (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1)
                                  (HEAP$1_4 HEAP$1_3))
                                 (let
                                    ((HEAP$1_5 HEAP$1_res_2)
                                     (STACK$1_3 STACK$1_res_2))
                                    (let
                                       ((_$1_2_1 (select_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                                       (let
                                          ((sub$1_0_1 (- _$1_2_1 1)))
                                          (let
                                             ((HEAP$1_6 (store_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                             (let
                                                ((_$1_3_1 (select_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                (let
                                                   ((inc$1_0_1 (+ _$1_3_1 1)))
                                                   (let
                                                      ((HEAP$1_7 (store_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 inc$1_0_1)))
                                                      (let
                                                         ((HEAP$1_8 HEAP$1_7))
                                                         (let
                                                            ((HEAP$1_9 HEAP$1_res_3)
                                                             (STACK$1_4 STACK$1_res_3)
                                                             (retval.0$1_0_1 call1$1_0_1))
                                                            (let
                                                               ((result$1_1 retval.0$1_0_1)
                                                                (HEAP$1_res_4 HEAP$1_9)
                                                                (STACK$1_res_4 STACK$1_4))
                                                               (=>
                                                                  (and
                                                                     (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                     cmp$1_0_1
                                                                     (not cmp$2_0_1)
                                                                     (INV_REC_rv_mult_int__int___1 5 _$1_1_1 HEAP$1_2 SP$1_1 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1)
                                                                     (INV_REC_bubble_sort__1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1 5 HEAP$1_4 SP$1_1 STACK$1_2 res1_1 HEAP$1_res_2 STACK$1_res_2)
                                                                     (INV_REC_Loop_foo_function_while1__1 a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 rvp_rvretval$1_0_1 rvp_rvretval$1_0_OnStack_1 HEAP$1_8 SP$1_1 STACK$1_3 call1$1_0_1 HEAP$1_res_3 STACK$1_res_3))
                                                                  (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_4 HEAP$2_res_1 STACK$1_res_4 STACK$2_res_1)))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (n$2_0_1 n$2_0_old_1)
                   (rvp_i$2_0_1 rvp_i$2_0_old_1)
                   (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                   (rvp_j$2_0_1 rvp_j$2_0_old_1)
                   (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                   (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
                   (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1)
                   (STACK$2_1 STACK$2_old_1))
                  (let
                     ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                     (let
                        ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
                        (let
                           ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1))
                            (HEAP$2_2 HEAP$2_1))
                           (let
                              ((HEAP$2_3 HEAP$2_res_1)
                               (STACK$2_2 STACK$2_res_1)
                               (idx.ext$2_0_1 call$2_0_1))
                              (let
                                 ((add.ptr$2_0_1 (+ a$2_0_1 (* 4 idx.ext$2_0_1)))
                                  (add.ptr$2_0_OnStack_1 a$2_0_OnStack_1)
                                  (HEAP$2_4 HEAP$2_3))
                                 (=>
                                    (and
                                       (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                       (not cmp$1_0_1)
                                       cmp$2_0_1
                                       (INV_REC_rv_mult_int__int___2 5 _$2_1_1 HEAP$2_2 SP$2_1 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1))
                                    (INV_REC_bubble_sort__2_PRE add.ptr$2_0_1 add.ptr$2_0_OnStack_1 5 HEAP$2_4 SP$2_1 STACK$2_2)))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (n$2_0_1 n$2_0_old_1)
                   (rvp_i$2_0_1 rvp_i$2_0_old_1)
                   (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                   (rvp_j$2_0_1 rvp_j$2_0_old_1)
                   (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                   (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
                   (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1)
                   (STACK$2_1 STACK$2_old_1))
                  (let
                     ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                     (let
                        ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
                        (let
                           ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1))
                            (HEAP$2_2 HEAP$2_1))
                           (let
                              ((HEAP$2_3 HEAP$2_res_1)
                               (STACK$2_2 STACK$2_res_1)
                               (idx.ext$2_0_1 call$2_0_1))
                              (let
                                 ((add.ptr$2_0_1 (+ a$2_0_1 (* 4 idx.ext$2_0_1)))
                                  (add.ptr$2_0_OnStack_1 a$2_0_OnStack_1)
                                  (HEAP$2_4 HEAP$2_3))
                                 (let
                                    ((HEAP$2_5 HEAP$2_res_2)
                                     (STACK$2_3 STACK$2_res_2))
                                    (let
                                       ((_$2_2_1 (select_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                                       (let
                                          ((inc$2_0_1 (+ _$2_2_1 1)))
                                          (let
                                             ((HEAP$2_6 (store_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 inc$2_0_1)))
                                             (let
                                                ((_$2_3_1 (select_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                (let
                                                   ((inc1$2_0_1 (+ _$2_3_1 1)))
                                                   (let
                                                      ((HEAP$2_7 (store_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc1$2_0_1)))
                                                      (let
                                                         ((HEAP$2_8 HEAP$2_7))
                                                         (=>
                                                            (and
                                                               (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                               (not cmp$1_0_1)
                                                               cmp$2_0_1
                                                               (INV_REC_rv_mult_int__int___2 5 _$2_1_1 HEAP$2_2 SP$2_1 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1)
                                                               (INV_REC_bubble_sort__2 add.ptr$2_0_1 add.ptr$2_0_OnStack_1 5 HEAP$2_4 SP$2_1 STACK$2_2 res2_1 HEAP$2_res_2 STACK$2_res_2))
                                                            (INV_REC_Loop_foo_function_while1__2_PRE a$2_0_1 a$2_0_OnStack_1 n$2_0_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 rvp_rvretval$2_0_1 rvp_rvretval$2_0_OnStack_1 HEAP$2_8 SP$2_1 STACK$2_3)))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (n$2_0_1 n$2_0_old_1)
                   (rvp_i$2_0_1 rvp_i$2_0_old_1)
                   (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                   (rvp_j$2_0_1 rvp_j$2_0_old_1)
                   (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                   (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
                   (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1)
                   (STACK$2_1 STACK$2_old_1))
                  (let
                     ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                     (let
                        ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
                        (let
                           ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1))
                            (HEAP$2_2 HEAP$2_1))
                           (let
                              ((HEAP$2_3 HEAP$2_res_1)
                               (STACK$2_2 STACK$2_res_1)
                               (idx.ext$2_0_1 call$2_0_1))
                              (let
                                 ((add.ptr$2_0_1 (+ a$2_0_1 (* 4 idx.ext$2_0_1)))
                                  (add.ptr$2_0_OnStack_1 a$2_0_OnStack_1)
                                  (HEAP$2_4 HEAP$2_3))
                                 (let
                                    ((HEAP$2_5 HEAP$2_res_2)
                                     (STACK$2_3 STACK$2_res_2))
                                    (let
                                       ((_$2_2_1 (select_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                                       (let
                                          ((inc$2_0_1 (+ _$2_2_1 1)))
                                          (let
                                             ((HEAP$2_6 (store_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 inc$2_0_1)))
                                             (let
                                                ((_$2_3_1 (select_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                (let
                                                   ((inc1$2_0_1 (+ _$2_3_1 1)))
                                                   (let
                                                      ((HEAP$2_7 (store_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc1$2_0_1)))
                                                      (let
                                                         ((HEAP$2_8 HEAP$2_7))
                                                         (let
                                                            ((HEAP$2_9 HEAP$2_res_3)
                                                             (STACK$2_4 STACK$2_res_3)
                                                             (retval.0$2_0_1 call2$2_0_1))
                                                            (let
                                                               ((result$2_1 retval.0$2_0_1)
                                                                (HEAP$2_res_4 HEAP$2_9)
                                                                (STACK$2_res_4 STACK$2_4))
                                                               (=>
                                                                  (and
                                                                     (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                     (not cmp$1_0_1)
                                                                     cmp$2_0_1
                                                                     (INV_REC_rv_mult_int__int___2 5 _$2_1_1 HEAP$2_2 SP$2_1 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1)
                                                                     (INV_REC_bubble_sort__2 add.ptr$2_0_1 add.ptr$2_0_OnStack_1 5 HEAP$2_4 SP$2_1 STACK$2_2 res2_1 HEAP$2_res_2 STACK$2_res_2)
                                                                     (INV_REC_Loop_foo_function_while1__2 a$2_0_1 a$2_0_OnStack_1 n$2_0_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 rvp_rvretval$2_0_1 rvp_rvretval$2_0_OnStack_1 HEAP$2_8 SP$2_1 STACK$2_3 call2$2_0_1 HEAP$2_res_3 STACK$2_res_3))
                                                                  (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_1 HEAP$2_res_4 STACK$1_res_1 STACK$2_res_4)))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1)
                   (a$2_0_1 a$2_0_old_1)
                   (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
                   (n$2_0_1 n$2_0_old_1)
                   (rvp_i$2_0_1 rvp_i$2_0_old_1)
                   (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
                   (rvp_j$2_0_1 rvp_j$2_0_old_1)
                   (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
                   (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
                   (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
                   (HEAP$2_1 HEAP$2_old_1)
                   (SP$2_1 SP$2_old_1)
                   (STACK$2_1 STACK$2_old_1))
                  (let
                     ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                     (let
                        ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
                        (let
                           ((retval.0$2_0_1 0))
                           (let
                              ((result$2_1 retval.0$2_0_1)
                               (HEAP$2_res_1 HEAP$2_1)
                               (STACK$2_res_1 STACK$2_1))
                              (=>
                                 (and
                                    (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                    (not cmp$1_0_1)
                                    (not cmp$2_0_1))
                                 (INV_REC_Loop_foo_function_while1^Loop_foo_function_while1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$1_1 result$2_1 HEAP$1_res_1 HEAP$2_res_1 STACK$1_res_1 STACK$2_res_1))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (sz$1_0_1 sz$1_0_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((i$1_0_1 SP$1_2)
             (i$1_0_OnStack_1 true)
             (sub$1_0_1 (- sz$1_0_1 1)))
            (let
               ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 i$1_0_1 i$1_0_OnStack_1 sub$1_0_1)))
               (let
                  ((HEAP$1_3 HEAP$1_2))
                  (=>
                     (INV_REC_bubble_sort__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 sz$1_0_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                     (INV_REC_Loop_bubble_sort_for1__1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 i$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (sz$1_0_1 sz$1_0_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((i$1_0_1 SP$1_2)
             (i$1_0_OnStack_1 true)
             (sub$1_0_1 (- sz$1_0_1 1)))
            (let
               ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 i$1_0_1 i$1_0_OnStack_1 sub$1_0_1)))
               (let
                  ((HEAP$1_3 HEAP$1_2))
                  (let
                     ((HEAP$1_4 HEAP$1_res_1)
                      (STACK$1_2 STACK$1_res_1))
                     (let
                        ((result$1_1 0)
                         (HEAP$1_res_2 HEAP$1_4)
                         (STACK$1_res_2 STACK$1_2))
                        (=>
                           (and
                              (INV_REC_bubble_sort__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 sz$1_0_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                              (INV_REC_Loop_bubble_sort_for1__1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 i$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1))
                           (INV_REC_bubble_sort__1 a$1_0_old_1 a$1_0_OnStack_old_1 sz$1_0_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 result$1_1 HEAP$1_res_2 STACK$1_res_2))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                  (let
                     ((_$1_1_1 (select_ HEAP$1_2 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1))
                      (HEAP$1_3 HEAP$1_2))
                     (=>
                        (and
                           (INV_REC_Loop_bubble_sort_for1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                           cmp$1_0_1)
                        (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_1 a$1_0_OnStack_1 _$1_1_1 j$1_0_1 j$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1)))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                  (let
                     ((_$1_1_1 (select_ HEAP$1_2 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1))
                      (HEAP$1_3 HEAP$1_2))
                     (let
                        ((HEAP$1_4 HEAP$1_res_1)
                         (STACK$1_2 STACK$1_res_1))
                        (let
                           ((_$1_2_1 (select_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                           (let
                              ((sub$1_0_1 (- _$1_2_1 1)))
                              (let
                                 ((HEAP$1_5 (store_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                 (let
                                    ((HEAP$1_6 HEAP$1_5))
                                    (=>
                                       (and
                                          (INV_REC_Loop_bubble_sort_for1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                                          cmp$1_0_1
                                          (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_1 a$1_0_OnStack_1 _$1_1_1 j$1_0_1 j$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1))
                                       (INV_REC_Loop_bubble_sort_for1__1_PRE a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 HEAP$1_6 SP$1_2 STACK$1_2))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 j$1_0_1 j$1_0_OnStack_1 0)))
                  (let
                     ((_$1_1_1 (select_ HEAP$1_2 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1))
                      (HEAP$1_3 HEAP$1_2))
                     (let
                        ((HEAP$1_4 HEAP$1_res_1)
                         (STACK$1_2 STACK$1_res_1))
                        (let
                           ((_$1_2_1 (select_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                           (let
                              ((sub$1_0_1 (- _$1_2_1 1)))
                              (let
                                 ((HEAP$1_5 (store_ HEAP$1_4 STACK$1_2 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                 (let
                                    ((HEAP$1_6 HEAP$1_5))
                                    (let
                                       ((HEAP$1_7 HEAP$1_res_2)
                                        (STACK$1_3 STACK$1_res_2)
                                        (retval.0$1_0_1 call1$1_0_1))
                                       (let
                                          ((result$1_1 retval.0$1_0_1)
                                           (HEAP$1_res_3 HEAP$1_7)
                                           (STACK$1_res_3 STACK$1_3))
                                          (=>
                                             (and
                                                (INV_REC_Loop_bubble_sort_for1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                                                cmp$1_0_1
                                                (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_1 a$1_0_OnStack_1 _$1_1_1 j$1_0_1 j$1_0_OnStack_1 HEAP$1_3 SP$1_2 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1)
                                                (INV_REC_Loop_bubble_sort_for1__1 a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 HEAP$1_6 SP$1_2 STACK$1_2 call1$1_0_1 HEAP$1_res_2 STACK$1_res_2))
                                             (INV_REC_Loop_bubble_sort_for1__1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 result$1_1 HEAP$1_res_3 STACK$1_res_3))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1))
      (let
         ((STACK$1_1 STACK$1_old_1)
          (SP$1_2 (- SP$1_1 4)))
         (let
            ((j$1_0_1 SP$1_2)
             (j$1_0_OnStack_1 true)
             (_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
            (let
               ((cmp$1_0_1 (> _$1_0_1 0)))
               (let
                  ((retval.0$1_0_1 0))
                  (let
                     ((result$1_1 retval.0$1_0_1)
                      (HEAP$1_res_1 HEAP$1_1)
                      (STACK$1_res_1 STACK$1_1))
                     (=>
                        (and
                           (INV_REC_Loop_bubble_sort_for1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                           (not cmp$1_0_1))
                        (INV_REC_Loop_bubble_sort_for1__1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 result$1_1 HEAP$1_res_1 STACK$1_res_1)))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_5_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((idx.ext6$1_0_1 _$1_5_1))
                                             (let
                                                ((add.ptr7$1_0_1 (+ a$1_0_1 (* 4 idx.ext6$1_0_1)))
                                                 (add.ptr7$1_0_OnStack_1 a$1_0_OnStack_1))
                                                (let
                                                   ((_$1_6_1 (select_ HEAP$1_1 STACK$1_1 add.ptr7$1_0_1 add.ptr7$1_0_OnStack_1))
                                                    (_$1_7_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                   (let
                                                      ((idx.ext8$1_0_1 _$1_7_1))
                                                      (let
                                                         ((add.ptr9$1_0_1 (+ a$1_0_1 (* 4 idx.ext8$1_0_1)))
                                                          (add.ptr9$1_0_OnStack_1 a$1_0_OnStack_1))
                                                         (let
                                                            ((add.ptr10$1_0_1 (+ add.ptr9$1_0_1 (* 4 1)))
                                                             (add.ptr10$1_0_OnStack_1 add.ptr9$1_0_OnStack_1))
                                                            (let
                                                               ((_$1_8_1 (select_ HEAP$1_1 STACK$1_1 add.ptr10$1_0_1 add.ptr10$1_0_OnStack_1))
                                                                (_$1_9_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                               (let
                                                                  ((idx.ext11$1_0_1 _$1_9_1))
                                                                  (let
                                                                     ((add.ptr12$1_0_1 (+ a$1_0_1 (* 4 idx.ext11$1_0_1)))
                                                                      (add.ptr12$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                     (let
                                                                        ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 add.ptr12$1_0_1 add.ptr12$1_0_OnStack_1 _$1_8_1)))
                                                                        (let
                                                                           ((_$1_10_1 (select_ HEAP$1_2 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                           (let
                                                                              ((idx.ext13$1_0_1 _$1_10_1))
                                                                              (let
                                                                                 ((add.ptr14$1_0_1 (+ a$1_0_1 (* 4 idx.ext13$1_0_1)))
                                                                                  (add.ptr14$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                                 (let
                                                                                    ((add.ptr15$1_0_1 (+ add.ptr14$1_0_1 (* 4 1)))
                                                                                     (add.ptr15$1_0_OnStack_1 add.ptr14$1_0_OnStack_1))
                                                                                    (let
                                                                                       ((HEAP$1_3 (store_ HEAP$1_2 STACK$1_1 add.ptr15$1_0_1 add.ptr15$1_0_OnStack_1 _$1_6_1)))
                                                                                       (let
                                                                                          ((_$1_11_1 (select_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                                          (let
                                                                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                                                                             (let
                                                                                                ((HEAP$1_4 (store_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                                                                (let
                                                                                                   ((HEAP$1_5 HEAP$1_4))
                                                                                                   (=>
                                                                                                      (and
                                                                                                         (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                                                                                                         cmp$1_0_1
                                                                                                         cmp4$1_0_1)
                                                                                                      (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_5 SP$1_1 STACK$1_1)))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_5_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((idx.ext6$1_0_1 _$1_5_1))
                                             (let
                                                ((add.ptr7$1_0_1 (+ a$1_0_1 (* 4 idx.ext6$1_0_1)))
                                                 (add.ptr7$1_0_OnStack_1 a$1_0_OnStack_1))
                                                (let
                                                   ((_$1_6_1 (select_ HEAP$1_1 STACK$1_1 add.ptr7$1_0_1 add.ptr7$1_0_OnStack_1))
                                                    (_$1_7_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                   (let
                                                      ((idx.ext8$1_0_1 _$1_7_1))
                                                      (let
                                                         ((add.ptr9$1_0_1 (+ a$1_0_1 (* 4 idx.ext8$1_0_1)))
                                                          (add.ptr9$1_0_OnStack_1 a$1_0_OnStack_1))
                                                         (let
                                                            ((add.ptr10$1_0_1 (+ add.ptr9$1_0_1 (* 4 1)))
                                                             (add.ptr10$1_0_OnStack_1 add.ptr9$1_0_OnStack_1))
                                                            (let
                                                               ((_$1_8_1 (select_ HEAP$1_1 STACK$1_1 add.ptr10$1_0_1 add.ptr10$1_0_OnStack_1))
                                                                (_$1_9_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                               (let
                                                                  ((idx.ext11$1_0_1 _$1_9_1))
                                                                  (let
                                                                     ((add.ptr12$1_0_1 (+ a$1_0_1 (* 4 idx.ext11$1_0_1)))
                                                                      (add.ptr12$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                     (let
                                                                        ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 add.ptr12$1_0_1 add.ptr12$1_0_OnStack_1 _$1_8_1)))
                                                                        (let
                                                                           ((_$1_10_1 (select_ HEAP$1_2 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                           (let
                                                                              ((idx.ext13$1_0_1 _$1_10_1))
                                                                              (let
                                                                                 ((add.ptr14$1_0_1 (+ a$1_0_1 (* 4 idx.ext13$1_0_1)))
                                                                                  (add.ptr14$1_0_OnStack_1 a$1_0_OnStack_1))
                                                                                 (let
                                                                                    ((add.ptr15$1_0_1 (+ add.ptr14$1_0_1 (* 4 1)))
                                                                                     (add.ptr15$1_0_OnStack_1 add.ptr14$1_0_OnStack_1))
                                                                                    (let
                                                                                       ((HEAP$1_3 (store_ HEAP$1_2 STACK$1_1 add.ptr15$1_0_1 add.ptr15$1_0_OnStack_1 _$1_6_1)))
                                                                                       (let
                                                                                          ((_$1_11_1 (select_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                                                                          (let
                                                                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                                                                             (let
                                                                                                ((HEAP$1_4 (store_ HEAP$1_3 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                                                                (let
                                                                                                   ((HEAP$1_5 HEAP$1_4))
                                                                                                   (let
                                                                                                      ((HEAP$1_6 HEAP$1_res_1)
                                                                                                       (STACK$1_2 STACK$1_res_1)
                                                                                                       (retval.0$1_0_1 call$1_0_1))
                                                                                                      (let
                                                                                                         ((result$1_1 retval.0$1_0_1)
                                                                                                          (HEAP$1_res_2 HEAP$1_6)
                                                                                                          (STACK$1_res_2 STACK$1_2))
                                                                                                         (=>
                                                                                                            (and
                                                                                                               (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                                                                                                               cmp$1_0_1
                                                                                                               cmp4$1_0_1
                                                                                                               (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_5 SP$1_1 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1))
                                                                                                            (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 result$1_1 HEAP$1_res_2 STACK$1_res_2)))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_11_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                             (let
                                                ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                (let
                                                   ((HEAP$1_3 HEAP$1_2))
                                                   (=>
                                                      (and
                                                         (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                                                         cmp$1_0_1
                                                         (not cmp4$1_0_1))
                                                      (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_3 SP$1_1 STACK$1_1)))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
               (let
                  ((idx.ext$1_0_1 _$1_1_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1))
                     (let
                        ((_$1_2_1 (select_ HEAP$1_1 STACK$1_1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1))
                         (_$1_3_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                        (let
                           ((idx.ext1$1_0_1 _$1_3_1))
                           (let
                              ((add.ptr2$1_0_1 (+ a$1_0_1 (* 4 idx.ext1$1_0_1)))
                               (add.ptr2$1_0_OnStack_1 a$1_0_OnStack_1))
                              (let
                                 ((add.ptr3$1_0_1 (+ add.ptr2$1_0_1 (* 4 1)))
                                  (add.ptr3$1_0_OnStack_1 add.ptr2$1_0_OnStack_1))
                                 (let
                                    ((_$1_4_1 (select_ HEAP$1_1 STACK$1_1 add.ptr3$1_0_1 add.ptr3$1_0_OnStack_1)))
                                    (let
                                       ((cmp4$1_0_1 (< _$1_2_1 _$1_4_1)))
                                       (let
                                          ((_$1_11_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                          (let
                                             ((add$1_0_1 (+ _$1_11_1 1)))
                                             (let
                                                ((HEAP$1_2 (store_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 add$1_0_1)))
                                                (let
                                                   ((HEAP$1_3 HEAP$1_2))
                                                   (let
                                                      ((HEAP$1_4 HEAP$1_res_1)
                                                       (STACK$1_2 STACK$1_res_1)
                                                       (retval.0$1_0_1 call$1_0_1))
                                                      (let
                                                         ((result$1_1 retval.0$1_0_1)
                                                          (HEAP$1_res_2 HEAP$1_4)
                                                          (STACK$1_res_2 STACK$1_2))
                                                         (=>
                                                            (and
                                                               (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                                                               cmp$1_0_1
                                                               (not cmp4$1_0_1)
                                                               (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_1 a$1_0_OnStack_1 i$1_0_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 HEAP$1_3 SP$1_1 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1))
                                                            (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 result$1_1 HEAP$1_res_2 STACK$1_res_2)))))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (i$1_0_1 i$1_0_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (< _$1_0_1 i$1_0_1)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1))
                  (=>
                     (and
                        (INV_REC_Loop_bubble_sort_for1_for1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                        (not cmp$1_0_1))
                     (INV_REC_Loop_bubble_sort_for1_for1__1 a$1_0_old_1 a$1_0_OnStack_old_1 i$1_0_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 result$1_1 HEAP$1_res_1 STACK$1_res_1))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1))
                (HEAP$1_2 HEAP$1_1))
               (let
                  ((HEAP$1_3 HEAP$1_res_1)
                   (STACK$1_2 STACK$1_res_1)
                   (idx.ext$1_0_1 call$1_0_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1)
                      (HEAP$1_4 HEAP$1_3))
                     (=>
                        (and
                           (INV_REC_Loop_foo_function_while1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                           cmp$1_0_1
                           (INV_REC_rv_mult_int__int___1 5 _$1_1_1 HEAP$1_2 SP$1_1 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1))
                        (INV_REC_bubble_sort__1_PRE add.ptr$1_0_1 add.ptr$1_0_OnStack_1 5 HEAP$1_4 SP$1_1 STACK$1_2)))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1))
                (HEAP$1_2 HEAP$1_1))
               (let
                  ((HEAP$1_3 HEAP$1_res_1)
                   (STACK$1_2 STACK$1_res_1)
                   (idx.ext$1_0_1 call$1_0_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1)
                      (HEAP$1_4 HEAP$1_3))
                     (let
                        ((HEAP$1_5 HEAP$1_res_2)
                         (STACK$1_3 STACK$1_res_2))
                        (let
                           ((_$1_2_1 (select_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                           (let
                              ((sub$1_0_1 (- _$1_2_1 1)))
                              (let
                                 ((HEAP$1_6 (store_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                 (let
                                    ((_$1_3_1 (select_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                    (let
                                       ((inc$1_0_1 (+ _$1_3_1 1)))
                                       (let
                                          ((HEAP$1_7 (store_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 inc$1_0_1)))
                                          (let
                                             ((HEAP$1_8 HEAP$1_7))
                                             (=>
                                                (and
                                                   (INV_REC_Loop_foo_function_while1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                                                   cmp$1_0_1
                                                   (INV_REC_rv_mult_int__int___1 5 _$1_1_1 HEAP$1_2 SP$1_1 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1)
                                                   (INV_REC_bubble_sort__1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1 5 HEAP$1_4 SP$1_1 STACK$1_2 res1_1 HEAP$1_res_2 STACK$1_res_2))
                                                (INV_REC_Loop_foo_function_while1__1_PRE a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 rvp_rvretval$1_0_1 rvp_rvretval$1_0_OnStack_1 HEAP$1_8 SP$1_1 STACK$1_3)))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((_$1_1_1 (select_ HEAP$1_1 STACK$1_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1))
                (HEAP$1_2 HEAP$1_1))
               (let
                  ((HEAP$1_3 HEAP$1_res_1)
                   (STACK$1_2 STACK$1_res_1)
                   (idx.ext$1_0_1 call$1_0_1))
                  (let
                     ((add.ptr$1_0_1 (+ a$1_0_1 (* 4 idx.ext$1_0_1)))
                      (add.ptr$1_0_OnStack_1 a$1_0_OnStack_1)
                      (HEAP$1_4 HEAP$1_3))
                     (let
                        ((HEAP$1_5 HEAP$1_res_2)
                         (STACK$1_3 STACK$1_res_2))
                        (let
                           ((_$1_2_1 (select_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
                           (let
                              ((sub$1_0_1 (- _$1_2_1 1)))
                              (let
                                 ((HEAP$1_6 (store_ HEAP$1_5 STACK$1_3 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 sub$1_0_1)))
                                 (let
                                    ((_$1_3_1 (select_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1)))
                                    (let
                                       ((inc$1_0_1 (+ _$1_3_1 1)))
                                       (let
                                          ((HEAP$1_7 (store_ HEAP$1_6 STACK$1_3 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 inc$1_0_1)))
                                          (let
                                             ((HEAP$1_8 HEAP$1_7))
                                             (let
                                                ((HEAP$1_9 HEAP$1_res_3)
                                                 (STACK$1_4 STACK$1_res_3)
                                                 (retval.0$1_0_1 call1$1_0_1))
                                                (let
                                                   ((result$1_1 retval.0$1_0_1)
                                                    (HEAP$1_res_4 HEAP$1_9)
                                                    (STACK$1_res_4 STACK$1_4))
                                                   (=>
                                                      (and
                                                         (INV_REC_Loop_foo_function_while1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                                                         cmp$1_0_1
                                                         (INV_REC_rv_mult_int__int___1 5 _$1_1_1 HEAP$1_2 SP$1_1 STACK$1_1 call$1_0_1 HEAP$1_res_1 STACK$1_res_1)
                                                         (INV_REC_bubble_sort__1 add.ptr$1_0_1 add.ptr$1_0_OnStack_1 5 HEAP$1_4 SP$1_1 STACK$1_2 res1_1 HEAP$1_res_2 STACK$1_res_2)
                                                         (INV_REC_Loop_foo_function_while1__1 a$1_0_1 a$1_0_OnStack_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1 rvp_j$1_0_1 rvp_j$1_0_OnStack_1 rvp_rvretval$1_0_1 rvp_rvretval$1_0_OnStack_1 HEAP$1_8 SP$1_1 STACK$1_3 call1$1_0_1 HEAP$1_res_3 STACK$1_res_3))
                                                      (INV_REC_Loop_foo_function_while1__1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 result$1_1 HEAP$1_res_4 STACK$1_res_4)))))))))))))))))))
(rule
   (let
      ((a$1_0_1 a$1_0_old_1)
       (a$1_0_OnStack_1 a$1_0_OnStack_old_1)
       (rvp_i$1_0_1 rvp_i$1_0_old_1)
       (rvp_i$1_0_OnStack_1 rvp_i$1_0_OnStack_old_1)
       (rvp_j$1_0_1 rvp_j$1_0_old_1)
       (rvp_j$1_0_OnStack_1 rvp_j$1_0_OnStack_old_1)
       (rvp_rvretval$1_0_1 rvp_rvretval$1_0_old_1)
       (rvp_rvretval$1_0_OnStack_1 rvp_rvretval$1_0_OnStack_old_1)
       (HEAP$1_1 HEAP$1_old_1)
       (SP$1_1 SP$1_old_1)
       (STACK$1_1 STACK$1_old_1))
      (let
         ((_$1_0_1 (select_ HEAP$1_1 STACK$1_1 rvp_i$1_0_1 rvp_i$1_0_OnStack_1)))
         (let
            ((cmp$1_0_1 (>= _$1_0_1 0)))
            (let
               ((retval.0$1_0_1 0))
               (let
                  ((result$1_1 retval.0$1_0_1)
                   (HEAP$1_res_1 HEAP$1_1)
                   (STACK$1_res_1 STACK$1_1))
                  (=>
                     (and
                        (INV_REC_Loop_foo_function_while1__1_PRE a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1)
                        (not cmp$1_0_1))
                     (INV_REC_Loop_foo_function_while1__1 a$1_0_old_1 a$1_0_OnStack_old_1 rvp_i$1_0_old_1 rvp_i$1_0_OnStack_old_1 rvp_j$1_0_old_1 rvp_j$1_0_OnStack_old_1 rvp_rvretval$1_0_old_1 rvp_rvretval$1_0_OnStack_old_1 HEAP$1_old_1 SP$1_old_1 STACK$1_old_1 result$1_1 HEAP$1_res_1 STACK$1_res_1))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (sz$2_0_1 sz$2_0_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1))
      (let
         ((STACK$2_1 STACK$2_old_1)
          (SP$2_2 (- SP$2_1 4)))
         (let
            ((i$2_0_1 SP$2_2)
             (i$2_0_OnStack_1 true)
             (sub$2_0_1 (- sz$2_0_1 1)))
            (let
               ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 i$2_0_1 i$2_0_OnStack_1 sub$2_0_1)))
               (let
                  ((HEAP$2_3 HEAP$2_2))
                  (=>
                     (INV_REC_bubble_sort__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 sz$2_0_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                     (INV_REC_Loop_bubble_sort_for1__2_PRE a$2_0_1 a$2_0_OnStack_1 i$2_0_1 i$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (sz$2_0_1 sz$2_0_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1))
      (let
         ((STACK$2_1 STACK$2_old_1)
          (SP$2_2 (- SP$2_1 4)))
         (let
            ((i$2_0_1 SP$2_2)
             (i$2_0_OnStack_1 true)
             (sub$2_0_1 (- sz$2_0_1 1)))
            (let
               ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 i$2_0_1 i$2_0_OnStack_1 sub$2_0_1)))
               (let
                  ((HEAP$2_3 HEAP$2_2))
                  (let
                     ((HEAP$2_4 HEAP$2_res_1)
                      (STACK$2_2 STACK$2_res_1))
                     (let
                        ((result$2_1 0)
                         (HEAP$2_res_2 HEAP$2_4)
                         (STACK$2_res_2 STACK$2_2))
                        (=>
                           (and
                              (INV_REC_bubble_sort__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 sz$2_0_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                              (INV_REC_Loop_bubble_sort_for1__2 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 i$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1))
                           (INV_REC_bubble_sort__2 a$2_0_old_1 a$2_0_OnStack_old_1 sz$2_0_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$2_1 HEAP$2_res_2 STACK$2_res_2))))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (rvp_i$2_0_1 rvp_i$2_0_old_1)
       (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1))
      (let
         ((STACK$2_1 STACK$2_old_1)
          (SP$2_2 (- SP$2_1 4)))
         (let
            ((j$2_0_1 SP$2_2)
             (j$2_0_OnStack_1 true)
             (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
            (let
               ((cmp$2_0_1 (> _$2_0_1 0)))
               (let
                  ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                  (let
                     ((_$2_1_1 (select_ HEAP$2_2 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1))
                      (HEAP$2_3 HEAP$2_2))
                     (=>
                        (and
                           (INV_REC_Loop_bubble_sort_for1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                           cmp$2_0_1)
                        (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_1 a$2_0_OnStack_1 _$2_1_1 j$2_0_1 j$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1)))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (rvp_i$2_0_1 rvp_i$2_0_old_1)
       (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1))
      (let
         ((STACK$2_1 STACK$2_old_1)
          (SP$2_2 (- SP$2_1 4)))
         (let
            ((j$2_0_1 SP$2_2)
             (j$2_0_OnStack_1 true)
             (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
            (let
               ((cmp$2_0_1 (> _$2_0_1 0)))
               (let
                  ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                  (let
                     ((_$2_1_1 (select_ HEAP$2_2 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1))
                      (HEAP$2_3 HEAP$2_2))
                     (let
                        ((HEAP$2_4 HEAP$2_res_1)
                         (STACK$2_2 STACK$2_res_1))
                        (let
                           ((_$2_2_1 (select_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((dec$2_0_1 (+ _$2_2_1 (- 1))))
                              (let
                                 ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 dec$2_0_1)))
                                 (let
                                    ((HEAP$2_6 HEAP$2_5))
                                    (=>
                                       (and
                                          (INV_REC_Loop_bubble_sort_for1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                          cmp$2_0_1
                                          (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_1 a$2_0_OnStack_1 _$2_1_1 j$2_0_1 j$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1))
                                       (INV_REC_Loop_bubble_sort_for1__2_PRE a$2_0_1 a$2_0_OnStack_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 HEAP$2_6 SP$2_2 STACK$2_2))))))))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (rvp_i$2_0_1 rvp_i$2_0_old_1)
       (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1))
      (let
         ((STACK$2_1 STACK$2_old_1)
          (SP$2_2 (- SP$2_1 4)))
         (let
            ((j$2_0_1 SP$2_2)
             (j$2_0_OnStack_1 true)
             (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
            (let
               ((cmp$2_0_1 (> _$2_0_1 0)))
               (let
                  ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 j$2_0_1 j$2_0_OnStack_1 0)))
                  (let
                     ((_$2_1_1 (select_ HEAP$2_2 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1))
                      (HEAP$2_3 HEAP$2_2))
                     (let
                        ((HEAP$2_4 HEAP$2_res_1)
                         (STACK$2_2 STACK$2_res_1))
                        (let
                           ((_$2_2_1 (select_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((dec$2_0_1 (+ _$2_2_1 (- 1))))
                              (let
                                 ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_2 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 dec$2_0_1)))
                                 (let
                                    ((HEAP$2_6 HEAP$2_5))
                                    (let
                                       ((HEAP$2_7 HEAP$2_res_2)
                                        (STACK$2_3 STACK$2_res_2)
                                        (retval.0$2_0_1 call1$2_0_1))
                                       (let
                                          ((result$2_1 retval.0$2_0_1)
                                           (HEAP$2_res_3 HEAP$2_7)
                                           (STACK$2_res_3 STACK$2_3))
                                          (=>
                                             (and
                                                (INV_REC_Loop_bubble_sort_for1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                cmp$2_0_1
                                                (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_1 a$2_0_OnStack_1 _$2_1_1 j$2_0_1 j$2_0_OnStack_1 HEAP$2_3 SP$2_2 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1)
                                                (INV_REC_Loop_bubble_sort_for1__2 a$2_0_1 a$2_0_OnStack_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 HEAP$2_6 SP$2_2 STACK$2_2 call1$2_0_1 HEAP$2_res_2 STACK$2_res_2))
                                             (INV_REC_Loop_bubble_sort_for1__2 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$2_1 HEAP$2_res_3 STACK$2_res_3))))))))))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (rvp_i$2_0_1 rvp_i$2_0_old_1)
       (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1))
      (let
         ((STACK$2_1 STACK$2_old_1)
          (SP$2_2 (- SP$2_1 4)))
         (let
            ((j$2_0_1 SP$2_2)
             (j$2_0_OnStack_1 true)
             (_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
            (let
               ((cmp$2_0_1 (> _$2_0_1 0)))
               (let
                  ((retval.0$2_0_1 0))
                  (let
                     ((result$2_1 retval.0$2_0_1)
                      (HEAP$2_res_1 HEAP$2_1)
                      (STACK$2_res_1 STACK$2_1))
                     (=>
                        (and
                           (INV_REC_Loop_bubble_sort_for1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                           (not cmp$2_0_1))
                        (INV_REC_Loop_bubble_sort_for1__2 a$2_0_old_1 a$2_0_OnStack_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$2_1 HEAP$2_res_1 STACK$2_res_1)))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (i$2_0_1 i$2_0_old_1)
       (rvp_j$2_0_1 rvp_j$2_0_old_1)
       (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1)
       (STACK$2_1 STACK$2_old_1))
      (let
         ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
         (let
            ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
            (let
               ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
               (let
                  ((idxprom$2_0_1 _$2_1_1))
                  (let
                     ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                      (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                     (let
                        ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                         (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                        (let
                           ((add$2_0_1 (+ _$2_3_1 1)))
                           (let
                              ((idxprom1$2_0_1 add$2_0_1))
                              (let
                                 ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                  (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                 (let
                                    ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                    (let
                                       ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                       (let
                                          ((_$2_5_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                          (let
                                             ((idxprom5$2_0_1 _$2_5_1))
                                             (let
                                                ((arrayidx6$2_0_1 (+ a$2_0_1 (* 4 idxprom5$2_0_1)))
                                                 (arrayidx6$2_0_OnStack_1 a$2_0_OnStack_1))
                                                (let
                                                   ((_$2_6_1 (select_ HEAP$2_1 STACK$2_1 arrayidx6$2_0_1 arrayidx6$2_0_OnStack_1))
                                                    (_$2_7_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                   (let
                                                      ((add7$2_0_1 (+ _$2_7_1 1)))
                                                      (let
                                                         ((idxprom8$2_0_1 add7$2_0_1))
                                                         (let
                                                            ((arrayidx9$2_0_1 (+ a$2_0_1 (* 4 idxprom8$2_0_1)))
                                                             (arrayidx9$2_0_OnStack_1 a$2_0_OnStack_1))
                                                            (let
                                                               ((_$2_8_1 (select_ HEAP$2_1 STACK$2_1 arrayidx9$2_0_1 arrayidx9$2_0_OnStack_1))
                                                                (_$2_9_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                               (let
                                                                  ((idxprom10$2_0_1 _$2_9_1))
                                                                  (let
                                                                     ((arrayidx11$2_0_1 (+ a$2_0_1 (* 4 idxprom10$2_0_1)))
                                                                      (arrayidx11$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                     (let
                                                                        ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 arrayidx11$2_0_1 arrayidx11$2_0_OnStack_1 _$2_8_1)))
                                                                        (let
                                                                           ((_$2_10_1 (select_ HEAP$2_2 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                           (let
                                                                              ((add12$2_0_1 (+ _$2_10_1 1)))
                                                                              (let
                                                                                 ((idxprom13$2_0_1 add12$2_0_1))
                                                                                 (let
                                                                                    ((arrayidx14$2_0_1 (+ a$2_0_1 (* 4 idxprom13$2_0_1)))
                                                                                     (arrayidx14$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                    (let
                                                                                       ((HEAP$2_3 (store_ HEAP$2_2 STACK$2_1 arrayidx14$2_0_1 arrayidx14$2_0_OnStack_1 _$2_6_1)))
                                                                                       (let
                                                                                          ((_$2_11_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                          (let
                                                                                             ((idxprom15$2_0_1 _$2_11_1))
                                                                                             (let
                                                                                                ((arrayidx16$2_0_1 (+ a$2_0_1 (* 4 idxprom15$2_0_1)))
                                                                                                 (arrayidx16$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                (let
                                                                                                   ((_$2_12_1 (select_ HEAP$2_3 STACK$2_1 arrayidx16$2_0_1 arrayidx16$2_0_OnStack_1))
                                                                                                    (_$2_13_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                   (let
                                                                                                      ((idxprom17$2_0_1 _$2_13_1))
                                                                                                      (let
                                                                                                         ((arrayidx18$2_0_1 (+ a$2_0_1 (* 4 idxprom17$2_0_1)))
                                                                                                          (arrayidx18$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                         (let
                                                                                                            ((HEAP$2_4 (store_ HEAP$2_3 STACK$2_1 arrayidx18$2_0_1 arrayidx18$2_0_OnStack_1 _$2_12_1)))
                                                                                                            (let
                                                                                                               ((_$2_14_1 (select_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                               (let
                                                                                                                  ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                                                  (let
                                                                                                                     ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                                                     (let
                                                                                                                        ((HEAP$2_6 HEAP$2_5))
                                                                                                                        (=>
                                                                                                                           (and
                                                                                                                              (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                              cmp$2_0_1
                                                                                                                              cmp3$2_0_1)
                                                                                                                           (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_6 SP$2_1 STACK$2_1))))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (i$2_0_1 i$2_0_old_1)
       (rvp_j$2_0_1 rvp_j$2_0_old_1)
       (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1)
       (STACK$2_1 STACK$2_old_1))
      (let
         ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
         (let
            ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
            (let
               ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
               (let
                  ((idxprom$2_0_1 _$2_1_1))
                  (let
                     ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                      (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                     (let
                        ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                         (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                        (let
                           ((add$2_0_1 (+ _$2_3_1 1)))
                           (let
                              ((idxprom1$2_0_1 add$2_0_1))
                              (let
                                 ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                  (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                 (let
                                    ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                    (let
                                       ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                       (let
                                          ((_$2_5_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                          (let
                                             ((idxprom5$2_0_1 _$2_5_1))
                                             (let
                                                ((arrayidx6$2_0_1 (+ a$2_0_1 (* 4 idxprom5$2_0_1)))
                                                 (arrayidx6$2_0_OnStack_1 a$2_0_OnStack_1))
                                                (let
                                                   ((_$2_6_1 (select_ HEAP$2_1 STACK$2_1 arrayidx6$2_0_1 arrayidx6$2_0_OnStack_1))
                                                    (_$2_7_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                   (let
                                                      ((add7$2_0_1 (+ _$2_7_1 1)))
                                                      (let
                                                         ((idxprom8$2_0_1 add7$2_0_1))
                                                         (let
                                                            ((arrayidx9$2_0_1 (+ a$2_0_1 (* 4 idxprom8$2_0_1)))
                                                             (arrayidx9$2_0_OnStack_1 a$2_0_OnStack_1))
                                                            (let
                                                               ((_$2_8_1 (select_ HEAP$2_1 STACK$2_1 arrayidx9$2_0_1 arrayidx9$2_0_OnStack_1))
                                                                (_$2_9_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                               (let
                                                                  ((idxprom10$2_0_1 _$2_9_1))
                                                                  (let
                                                                     ((arrayidx11$2_0_1 (+ a$2_0_1 (* 4 idxprom10$2_0_1)))
                                                                      (arrayidx11$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                     (let
                                                                        ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 arrayidx11$2_0_1 arrayidx11$2_0_OnStack_1 _$2_8_1)))
                                                                        (let
                                                                           ((_$2_10_1 (select_ HEAP$2_2 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                           (let
                                                                              ((add12$2_0_1 (+ _$2_10_1 1)))
                                                                              (let
                                                                                 ((idxprom13$2_0_1 add12$2_0_1))
                                                                                 (let
                                                                                    ((arrayidx14$2_0_1 (+ a$2_0_1 (* 4 idxprom13$2_0_1)))
                                                                                     (arrayidx14$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                    (let
                                                                                       ((HEAP$2_3 (store_ HEAP$2_2 STACK$2_1 arrayidx14$2_0_1 arrayidx14$2_0_OnStack_1 _$2_6_1)))
                                                                                       (let
                                                                                          ((_$2_11_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                          (let
                                                                                             ((idxprom15$2_0_1 _$2_11_1))
                                                                                             (let
                                                                                                ((arrayidx16$2_0_1 (+ a$2_0_1 (* 4 idxprom15$2_0_1)))
                                                                                                 (arrayidx16$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                (let
                                                                                                   ((_$2_12_1 (select_ HEAP$2_3 STACK$2_1 arrayidx16$2_0_1 arrayidx16$2_0_OnStack_1))
                                                                                                    (_$2_13_1 (select_ HEAP$2_3 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                   (let
                                                                                                      ((idxprom17$2_0_1 _$2_13_1))
                                                                                                      (let
                                                                                                         ((arrayidx18$2_0_1 (+ a$2_0_1 (* 4 idxprom17$2_0_1)))
                                                                                                          (arrayidx18$2_0_OnStack_1 a$2_0_OnStack_1))
                                                                                                         (let
                                                                                                            ((HEAP$2_4 (store_ HEAP$2_3 STACK$2_1 arrayidx18$2_0_1 arrayidx18$2_0_OnStack_1 _$2_12_1)))
                                                                                                            (let
                                                                                                               ((_$2_14_1 (select_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                                                                                               (let
                                                                                                                  ((inc$2_0_1 (+ _$2_14_1 1)))
                                                                                                                  (let
                                                                                                                     ((HEAP$2_5 (store_ HEAP$2_4 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                                                                                     (let
                                                                                                                        ((HEAP$2_6 HEAP$2_5))
                                                                                                                        (let
                                                                                                                           ((HEAP$2_7 HEAP$2_res_1)
                                                                                                                            (STACK$2_2 STACK$2_res_1)
                                                                                                                            (retval.0$2_0_1 call$2_0_1))
                                                                                                                           (let
                                                                                                                              ((result$2_1 retval.0$2_0_1)
                                                                                                                               (HEAP$2_res_2 HEAP$2_7)
                                                                                                                               (STACK$2_res_2 STACK$2_2))
                                                                                                                              (=>
                                                                                                                                 (and
                                                                                                                                    (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                                                                                                    cmp$2_0_1
                                                                                                                                    cmp3$2_0_1
                                                                                                                                    (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_6 SP$2_1 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1))
                                                                                                                                 (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$2_1 HEAP$2_res_2 STACK$2_res_2))))))))))))))))))))))))))))))))))))))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (i$2_0_1 i$2_0_old_1)
       (rvp_j$2_0_1 rvp_j$2_0_old_1)
       (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1)
       (STACK$2_1 STACK$2_old_1))
      (let
         ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
         (let
            ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
            (let
               ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
               (let
                  ((idxprom$2_0_1 _$2_1_1))
                  (let
                     ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                      (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                     (let
                        ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                         (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                        (let
                           ((add$2_0_1 (+ _$2_3_1 1)))
                           (let
                              ((idxprom1$2_0_1 add$2_0_1))
                              (let
                                 ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                  (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                 (let
                                    ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                    (let
                                       ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                       (let
                                          ((_$2_14_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                          (let
                                             ((inc$2_0_1 (+ _$2_14_1 1)))
                                             (let
                                                ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                (let
                                                   ((HEAP$2_3 HEAP$2_2))
                                                   (=>
                                                      (and
                                                         (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                         cmp$2_0_1
                                                         (not cmp3$2_0_1))
                                                      (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_3 SP$2_1 STACK$2_1)))))))))))))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (i$2_0_1 i$2_0_old_1)
       (rvp_j$2_0_1 rvp_j$2_0_old_1)
       (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1)
       (STACK$2_1 STACK$2_old_1))
      (let
         ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
         (let
            ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
            (let
               ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
               (let
                  ((idxprom$2_0_1 _$2_1_1))
                  (let
                     ((arrayidx$2_0_1 (+ a$2_0_1 (* 4 idxprom$2_0_1)))
                      (arrayidx$2_0_OnStack_1 a$2_0_OnStack_1))
                     (let
                        ((_$2_2_1 (select_ HEAP$2_1 STACK$2_1 arrayidx$2_0_1 arrayidx$2_0_OnStack_1))
                         (_$2_3_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                        (let
                           ((add$2_0_1 (+ _$2_3_1 1)))
                           (let
                              ((idxprom1$2_0_1 add$2_0_1))
                              (let
                                 ((arrayidx2$2_0_1 (+ a$2_0_1 (* 4 idxprom1$2_0_1)))
                                  (arrayidx2$2_0_OnStack_1 a$2_0_OnStack_1))
                                 (let
                                    ((_$2_4_1 (select_ HEAP$2_1 STACK$2_1 arrayidx2$2_0_1 arrayidx2$2_0_OnStack_1)))
                                    (let
                                       ((cmp3$2_0_1 (< _$2_2_1 _$2_4_1)))
                                       (let
                                          ((_$2_14_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                          (let
                                             ((inc$2_0_1 (+ _$2_14_1 1)))
                                             (let
                                                ((HEAP$2_2 (store_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc$2_0_1)))
                                                (let
                                                   ((HEAP$2_3 HEAP$2_2))
                                                   (let
                                                      ((HEAP$2_4 HEAP$2_res_1)
                                                       (STACK$2_2 STACK$2_res_1)
                                                       (retval.0$2_0_1 call$2_0_1))
                                                      (let
                                                         ((result$2_1 retval.0$2_0_1)
                                                          (HEAP$2_res_2 HEAP$2_4)
                                                          (STACK$2_res_2 STACK$2_2))
                                                         (=>
                                                            (and
                                                               (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                               cmp$2_0_1
                                                               (not cmp3$2_0_1)
                                                               (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_1 a$2_0_OnStack_1 i$2_0_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 HEAP$2_3 SP$2_1 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1))
                                                            (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$2_1 HEAP$2_res_2 STACK$2_res_2)))))))))))))))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (i$2_0_1 i$2_0_old_1)
       (rvp_j$2_0_1 rvp_j$2_0_old_1)
       (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1)
       (STACK$2_1 STACK$2_old_1))
      (let
         ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
         (let
            ((cmp$2_0_1 (< _$2_0_1 i$2_0_1)))
            (let
               ((retval.0$2_0_1 0))
               (let
                  ((result$2_1 retval.0$2_0_1)
                   (HEAP$2_res_1 HEAP$2_1)
                   (STACK$2_res_1 STACK$2_1))
                  (=>
                     (and
                        (INV_REC_Loop_bubble_sort_for1_for1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                        (not cmp$2_0_1))
                     (INV_REC_Loop_bubble_sort_for1_for1__2 a$2_0_old_1 a$2_0_OnStack_old_1 i$2_0_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$2_1 HEAP$2_res_1 STACK$2_res_1))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (n$2_0_1 n$2_0_old_1)
       (rvp_i$2_0_1 rvp_i$2_0_old_1)
       (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
       (rvp_j$2_0_1 rvp_j$2_0_old_1)
       (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
       (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
       (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1)
       (STACK$2_1 STACK$2_old_1))
      (let
         ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
         (let
            ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
            (let
               ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1))
                (HEAP$2_2 HEAP$2_1))
               (let
                  ((HEAP$2_3 HEAP$2_res_1)
                   (STACK$2_2 STACK$2_res_1)
                   (idx.ext$2_0_1 call$2_0_1))
                  (let
                     ((add.ptr$2_0_1 (+ a$2_0_1 (* 4 idx.ext$2_0_1)))
                      (add.ptr$2_0_OnStack_1 a$2_0_OnStack_1)
                      (HEAP$2_4 HEAP$2_3))
                     (=>
                        (and
                           (INV_REC_Loop_foo_function_while1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                           cmp$2_0_1
                           (INV_REC_rv_mult_int__int___2 5 _$2_1_1 HEAP$2_2 SP$2_1 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1))
                        (INV_REC_bubble_sort__2_PRE add.ptr$2_0_1 add.ptr$2_0_OnStack_1 5 HEAP$2_4 SP$2_1 STACK$2_2)))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (n$2_0_1 n$2_0_old_1)
       (rvp_i$2_0_1 rvp_i$2_0_old_1)
       (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
       (rvp_j$2_0_1 rvp_j$2_0_old_1)
       (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
       (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
       (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1)
       (STACK$2_1 STACK$2_old_1))
      (let
         ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
         (let
            ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
            (let
               ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1))
                (HEAP$2_2 HEAP$2_1))
               (let
                  ((HEAP$2_3 HEAP$2_res_1)
                   (STACK$2_2 STACK$2_res_1)
                   (idx.ext$2_0_1 call$2_0_1))
                  (let
                     ((add.ptr$2_0_1 (+ a$2_0_1 (* 4 idx.ext$2_0_1)))
                      (add.ptr$2_0_OnStack_1 a$2_0_OnStack_1)
                      (HEAP$2_4 HEAP$2_3))
                     (let
                        ((HEAP$2_5 HEAP$2_res_2)
                         (STACK$2_3 STACK$2_res_2))
                        (let
                           ((_$2_2_1 (select_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((inc$2_0_1 (+ _$2_2_1 1)))
                              (let
                                 ((HEAP$2_6 (store_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 inc$2_0_1)))
                                 (let
                                    ((_$2_3_1 (select_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                    (let
                                       ((inc1$2_0_1 (+ _$2_3_1 1)))
                                       (let
                                          ((HEAP$2_7 (store_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc1$2_0_1)))
                                          (let
                                             ((HEAP$2_8 HEAP$2_7))
                                             (=>
                                                (and
                                                   (INV_REC_Loop_foo_function_while1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                   cmp$2_0_1
                                                   (INV_REC_rv_mult_int__int___2 5 _$2_1_1 HEAP$2_2 SP$2_1 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1)
                                                   (INV_REC_bubble_sort__2 add.ptr$2_0_1 add.ptr$2_0_OnStack_1 5 HEAP$2_4 SP$2_1 STACK$2_2 res2_1 HEAP$2_res_2 STACK$2_res_2))
                                                (INV_REC_Loop_foo_function_while1__2_PRE a$2_0_1 a$2_0_OnStack_1 n$2_0_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 rvp_rvretval$2_0_1 rvp_rvretval$2_0_OnStack_1 HEAP$2_8 SP$2_1 STACK$2_3)))))))))))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (n$2_0_1 n$2_0_old_1)
       (rvp_i$2_0_1 rvp_i$2_0_old_1)
       (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
       (rvp_j$2_0_1 rvp_j$2_0_old_1)
       (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
       (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
       (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1)
       (STACK$2_1 STACK$2_old_1))
      (let
         ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
         (let
            ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
            (let
               ((_$2_1_1 (select_ HEAP$2_1 STACK$2_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1))
                (HEAP$2_2 HEAP$2_1))
               (let
                  ((HEAP$2_3 HEAP$2_res_1)
                   (STACK$2_2 STACK$2_res_1)
                   (idx.ext$2_0_1 call$2_0_1))
                  (let
                     ((add.ptr$2_0_1 (+ a$2_0_1 (* 4 idx.ext$2_0_1)))
                      (add.ptr$2_0_OnStack_1 a$2_0_OnStack_1)
                      (HEAP$2_4 HEAP$2_3))
                     (let
                        ((HEAP$2_5 HEAP$2_res_2)
                         (STACK$2_3 STACK$2_res_2))
                        (let
                           ((_$2_2_1 (select_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
                           (let
                              ((inc$2_0_1 (+ _$2_2_1 1)))
                              (let
                                 ((HEAP$2_6 (store_ HEAP$2_5 STACK$2_3 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 inc$2_0_1)))
                                 (let
                                    ((_$2_3_1 (select_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1)))
                                    (let
                                       ((inc1$2_0_1 (+ _$2_3_1 1)))
                                       (let
                                          ((HEAP$2_7 (store_ HEAP$2_6 STACK$2_3 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 inc1$2_0_1)))
                                          (let
                                             ((HEAP$2_8 HEAP$2_7))
                                             (let
                                                ((HEAP$2_9 HEAP$2_res_3)
                                                 (STACK$2_4 STACK$2_res_3)
                                                 (retval.0$2_0_1 call2$2_0_1))
                                                (let
                                                   ((result$2_1 retval.0$2_0_1)
                                                    (HEAP$2_res_4 HEAP$2_9)
                                                    (STACK$2_res_4 STACK$2_4))
                                                   (=>
                                                      (and
                                                         (INV_REC_Loop_foo_function_while1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                                                         cmp$2_0_1
                                                         (INV_REC_rv_mult_int__int___2 5 _$2_1_1 HEAP$2_2 SP$2_1 STACK$2_1 call$2_0_1 HEAP$2_res_1 STACK$2_res_1)
                                                         (INV_REC_bubble_sort__2 add.ptr$2_0_1 add.ptr$2_0_OnStack_1 5 HEAP$2_4 SP$2_1 STACK$2_2 res2_1 HEAP$2_res_2 STACK$2_res_2)
                                                         (INV_REC_Loop_foo_function_while1__2 a$2_0_1 a$2_0_OnStack_1 n$2_0_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1 rvp_j$2_0_1 rvp_j$2_0_OnStack_1 rvp_rvretval$2_0_1 rvp_rvretval$2_0_OnStack_1 HEAP$2_8 SP$2_1 STACK$2_3 call2$2_0_1 HEAP$2_res_3 STACK$2_res_3))
                                                      (INV_REC_Loop_foo_function_while1__2 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$2_1 HEAP$2_res_4 STACK$2_res_4)))))))))))))))))))
(rule
   (let
      ((a$2_0_1 a$2_0_old_1)
       (a$2_0_OnStack_1 a$2_0_OnStack_old_1)
       (n$2_0_1 n$2_0_old_1)
       (rvp_i$2_0_1 rvp_i$2_0_old_1)
       (rvp_i$2_0_OnStack_1 rvp_i$2_0_OnStack_old_1)
       (rvp_j$2_0_1 rvp_j$2_0_old_1)
       (rvp_j$2_0_OnStack_1 rvp_j$2_0_OnStack_old_1)
       (rvp_rvretval$2_0_1 rvp_rvretval$2_0_old_1)
       (rvp_rvretval$2_0_OnStack_1 rvp_rvretval$2_0_OnStack_old_1)
       (HEAP$2_1 HEAP$2_old_1)
       (SP$2_1 SP$2_old_1)
       (STACK$2_1 STACK$2_old_1))
      (let
         ((_$2_0_1 (select_ HEAP$2_1 STACK$2_1 rvp_i$2_0_1 rvp_i$2_0_OnStack_1)))
         (let
            ((cmp$2_0_1 (<= _$2_0_1 n$2_0_1)))
            (let
               ((retval.0$2_0_1 0))
               (let
                  ((result$2_1 retval.0$2_0_1)
                   (HEAP$2_res_1 HEAP$2_1)
                   (STACK$2_res_1 STACK$2_1))
                  (=>
                     (and
                        (INV_REC_Loop_foo_function_while1__2_PRE a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1)
                        (not cmp$2_0_1))
                     (INV_REC_Loop_foo_function_while1__2 a$2_0_old_1 a$2_0_OnStack_old_1 n$2_0_old_1 rvp_i$2_0_old_1 rvp_i$2_0_OnStack_old_1 rvp_j$2_0_old_1 rvp_j$2_0_OnStack_old_1 rvp_rvretval$2_0_old_1 rvp_rvretval$2_0_OnStack_old_1 HEAP$2_old_1 SP$2_old_1 STACK$2_old_1 result$2_1 HEAP$2_res_1 STACK$2_res_1))))))))
(query
   END_QUERY
   :print-certificate
   true)
