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
   INV_REC_fact^fact
   (Int
    Int
    Int
    Int))
(declare-rel
   INV_REC_fact^fact_PRE
   (Int
    Int))
(declare-rel
   INV_REC_fact__1
   (Int
    Int))
(declare-rel
   INV_REC_fact__1_PRE
   (Int))
(declare-rel
   INV_REC_fact__2
   (Int
    Int))
(declare-rel
   INV_REC_fact__2_PRE
   (Int))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((retval.0$1_0_1 1))
            (let
               ((result$1_1 retval.0$1_0_1)
                (n$2_0_1 n$2_0_old_1))
               (let
                  ((cmp$2_0_1 (<= n$2_0_1 0)))
                  (let
                     ((retval.0$2_0_1 1))
                     (let
                        ((result$2_1 retval.0$2_0_1))
                        (=>
                           (and
                              (IN_INV n$1_0_old_1 n$2_0_old_1)
                              cmp$1_0_1
                              cmp$2_0_1
                              (not (OUT_INV result$1_1 result$2_1)))
                           END_QUERY)))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((retval.0$1_0_1 1))
            (let
               ((result$1_1 retval.0$1_0_1)
                (n$2_0_1 n$2_0_old_1))
               (let
                  ((cmp$2_0_1 (<= n$2_0_1 0)))
                  (let
                     ((sub$2_0_1 (- n$2_0_1 1)))
                     (=>
                        (and
                           (IN_INV n$1_0_old_1 n$2_0_old_1)
                           cmp$1_0_1
                           (not cmp$2_0_1))
                        (INV_REC_fact__2_PRE sub$2_0_1)))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((retval.0$1_0_1 1))
            (let
               ((result$1_1 retval.0$1_0_1)
                (n$2_0_1 n$2_0_old_1))
               (let
                  ((cmp$2_0_1 (<= n$2_0_1 0)))
                  (let
                     ((sub$2_0_1 (- n$2_0_1 1)))
                     (let
                        ((mul$2_0_1 (* n$2_0_1 call$2_0_1)))
                        (let
                           ((retval.0$2_0_1 mul$2_0_1))
                           (let
                              ((result$2_1 retval.0$2_0_1))
                              (=>
                                 (and
                                    (IN_INV n$1_0_old_1 n$2_0_old_1)
                                    cmp$1_0_1
                                    (not cmp$2_0_1)
                                    (INV_REC_fact__2 sub$2_0_1 call$2_0_1)
                                    (not (OUT_INV result$1_1 result$2_1)))
                                 END_QUERY)))))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((sub$1_0_1 (- n$1_0_1 1))
             (n$2_0_1 n$2_0_old_1))
            (let
               ((cmp$2_0_1 (<= n$2_0_1 0)))
               (let
                  ((retval.0$2_0_1 1))
                  (let
                     ((result$2_1 retval.0$2_0_1))
                     (=>
                        (and
                           (IN_INV n$1_0_old_1 n$2_0_old_1)
                           (not cmp$1_0_1)
                           cmp$2_0_1)
                        (INV_REC_fact__1_PRE sub$1_0_1)))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((sub$1_0_1 (- n$1_0_1 1))
             (n$2_0_1 n$2_0_old_1))
            (let
               ((cmp$2_0_1 (<= n$2_0_1 0)))
               (let
                  ((retval.0$2_0_1 1))
                  (let
                     ((result$2_1 retval.0$2_0_1))
                     (let
                        ((mul$1_0_1 (* n$1_0_1 call$1_0_1)))
                        (let
                           ((retval.0$1_0_1 mul$1_0_1))
                           (let
                              ((result$1_1 retval.0$1_0_1))
                              (=>
                                 (and
                                    (IN_INV n$1_0_old_1 n$2_0_old_1)
                                    (not cmp$1_0_1)
                                    cmp$2_0_1
                                    (INV_REC_fact__1 sub$1_0_1 call$1_0_1)
                                    (not (OUT_INV result$1_1 result$2_1)))
                                 END_QUERY)))))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((sub$1_0_1 (- n$1_0_1 1))
             (n$2_0_1 n$2_0_old_1))
            (let
               ((cmp$2_0_1 (<= n$2_0_1 0)))
               (let
                  ((sub$2_0_1 (- n$2_0_1 1)))
                  (=>
                     (and
                        (IN_INV n$1_0_old_1 n$2_0_old_1)
                        (not cmp$1_0_1)
                        (not cmp$2_0_1))
                     (INV_REC_fact^fact_PRE sub$1_0_1 sub$2_0_1))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((sub$1_0_1 (- n$1_0_1 1))
             (n$2_0_1 n$2_0_old_1))
            (let
               ((cmp$2_0_1 (<= n$2_0_1 0)))
               (let
                  ((sub$2_0_1 (- n$2_0_1 1)))
                  (let
                     ((mul$1_0_1 (* n$1_0_1 call$1_0_1)))
                     (let
                        ((retval.0$1_0_1 mul$1_0_1))
                        (let
                           ((result$1_1 retval.0$1_0_1)
                            (mul$2_0_1 (* n$2_0_1 call$2_0_1)))
                           (let
                              ((retval.0$2_0_1 mul$2_0_1))
                              (let
                                 ((result$2_1 retval.0$2_0_1))
                                 (=>
                                    (and
                                       (IN_INV n$1_0_old_1 n$2_0_old_1)
                                       (not cmp$1_0_1)
                                       (not cmp$2_0_1)
                                       (INV_REC_fact^fact sub$1_0_1 sub$2_0_1 call$1_0_1 call$2_0_1)
                                       (not (OUT_INV result$1_1 result$2_1)))
                                    END_QUERY))))))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((retval.0$1_0_1 1))
            (let
               ((result$1_1 retval.0$1_0_1)
                (n$2_0_1 n$2_0_old_1))
               (let
                  ((cmp$2_0_1 (<= n$2_0_1 0)))
                  (let
                     ((retval.0$2_0_1 1))
                     (let
                        ((result$2_1 retval.0$2_0_1))
                        (=>
                           (and
                              (INV_REC_fact^fact_PRE n$1_0_old_1 n$2_0_old_1)
                              cmp$1_0_1
                              cmp$2_0_1)
                           (INV_REC_fact^fact n$1_0_old_1 n$2_0_old_1 result$1_1 result$2_1))))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((retval.0$1_0_1 1))
            (let
               ((result$1_1 retval.0$1_0_1)
                (n$2_0_1 n$2_0_old_1))
               (let
                  ((cmp$2_0_1 (<= n$2_0_1 0)))
                  (let
                     ((sub$2_0_1 (- n$2_0_1 1)))
                     (=>
                        (and
                           (INV_REC_fact^fact_PRE n$1_0_old_1 n$2_0_old_1)
                           cmp$1_0_1
                           (not cmp$2_0_1))
                        (INV_REC_fact__2_PRE sub$2_0_1)))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((retval.0$1_0_1 1))
            (let
               ((result$1_1 retval.0$1_0_1)
                (n$2_0_1 n$2_0_old_1))
               (let
                  ((cmp$2_0_1 (<= n$2_0_1 0)))
                  (let
                     ((sub$2_0_1 (- n$2_0_1 1)))
                     (let
                        ((mul$2_0_1 (* n$2_0_1 call$2_0_1)))
                        (let
                           ((retval.0$2_0_1 mul$2_0_1))
                           (let
                              ((result$2_1 retval.0$2_0_1))
                              (=>
                                 (and
                                    (INV_REC_fact^fact_PRE n$1_0_old_1 n$2_0_old_1)
                                    cmp$1_0_1
                                    (not cmp$2_0_1)
                                    (INV_REC_fact__2 sub$2_0_1 call$2_0_1))
                                 (INV_REC_fact^fact n$1_0_old_1 n$2_0_old_1 result$1_1 result$2_1))))))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((sub$1_0_1 (- n$1_0_1 1))
             (n$2_0_1 n$2_0_old_1))
            (let
               ((cmp$2_0_1 (<= n$2_0_1 0)))
               (let
                  ((retval.0$2_0_1 1))
                  (let
                     ((result$2_1 retval.0$2_0_1))
                     (=>
                        (and
                           (INV_REC_fact^fact_PRE n$1_0_old_1 n$2_0_old_1)
                           (not cmp$1_0_1)
                           cmp$2_0_1)
                        (INV_REC_fact__1_PRE sub$1_0_1)))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((sub$1_0_1 (- n$1_0_1 1))
             (n$2_0_1 n$2_0_old_1))
            (let
               ((cmp$2_0_1 (<= n$2_0_1 0)))
               (let
                  ((retval.0$2_0_1 1))
                  (let
                     ((result$2_1 retval.0$2_0_1))
                     (let
                        ((mul$1_0_1 (* n$1_0_1 call$1_0_1)))
                        (let
                           ((retval.0$1_0_1 mul$1_0_1))
                           (let
                              ((result$1_1 retval.0$1_0_1))
                              (=>
                                 (and
                                    (INV_REC_fact^fact_PRE n$1_0_old_1 n$2_0_old_1)
                                    (not cmp$1_0_1)
                                    cmp$2_0_1
                                    (INV_REC_fact__1 sub$1_0_1 call$1_0_1))
                                 (INV_REC_fact^fact n$1_0_old_1 n$2_0_old_1 result$1_1 result$2_1))))))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((sub$1_0_1 (- n$1_0_1 1))
             (n$2_0_1 n$2_0_old_1))
            (let
               ((cmp$2_0_1 (<= n$2_0_1 0)))
               (let
                  ((sub$2_0_1 (- n$2_0_1 1)))
                  (=>
                     (and
                        (INV_REC_fact^fact_PRE n$1_0_old_1 n$2_0_old_1)
                        (not cmp$1_0_1)
                        (not cmp$2_0_1))
                     (INV_REC_fact^fact_PRE sub$1_0_1 sub$2_0_1))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((sub$1_0_1 (- n$1_0_1 1))
             (n$2_0_1 n$2_0_old_1))
            (let
               ((cmp$2_0_1 (<= n$2_0_1 0)))
               (let
                  ((sub$2_0_1 (- n$2_0_1 1)))
                  (let
                     ((mul$1_0_1 (* n$1_0_1 call$1_0_1)))
                     (let
                        ((retval.0$1_0_1 mul$1_0_1))
                        (let
                           ((result$1_1 retval.0$1_0_1)
                            (mul$2_0_1 (* n$2_0_1 call$2_0_1)))
                           (let
                              ((retval.0$2_0_1 mul$2_0_1))
                              (let
                                 ((result$2_1 retval.0$2_0_1))
                                 (=>
                                    (and
                                       (INV_REC_fact^fact_PRE n$1_0_old_1 n$2_0_old_1)
                                       (not cmp$1_0_1)
                                       (not cmp$2_0_1)
                                       (INV_REC_fact^fact sub$1_0_1 sub$2_0_1 call$1_0_1 call$2_0_1))
                                    (INV_REC_fact^fact n$1_0_old_1 n$2_0_old_1 result$1_1 result$2_1)))))))))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((retval.0$1_0_1 1))
            (let
               ((result$1_1 retval.0$1_0_1))
               (=>
                  (and
                     (INV_REC_fact__1_PRE n$1_0_old_1)
                     cmp$1_0_1)
                  (INV_REC_fact__1 n$1_0_old_1 result$1_1)))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((sub$1_0_1 (- n$1_0_1 1)))
            (=>
               (and
                  (INV_REC_fact__1_PRE n$1_0_old_1)
                  (not cmp$1_0_1))
               (INV_REC_fact__1_PRE sub$1_0_1))))))
(rule
   (let
      ((n$1_0_1 n$1_0_old_1))
      (let
         ((cmp$1_0_1 (<= n$1_0_1 1)))
         (let
            ((sub$1_0_1 (- n$1_0_1 1)))
            (let
               ((mul$1_0_1 (* n$1_0_1 call$1_0_1)))
               (let
                  ((retval.0$1_0_1 mul$1_0_1))
                  (let
                     ((result$1_1 retval.0$1_0_1))
                     (=>
                        (and
                           (INV_REC_fact__1_PRE n$1_0_old_1)
                           (not cmp$1_0_1)
                           (INV_REC_fact__1 sub$1_0_1 call$1_0_1))
                        (INV_REC_fact__1 n$1_0_old_1 result$1_1)))))))))
(rule
   (let
      ((n$2_0_1 n$2_0_old_1))
      (let
         ((cmp$2_0_1 (<= n$2_0_1 0)))
         (let
            ((retval.0$2_0_1 1))
            (let
               ((result$2_1 retval.0$2_0_1))
               (=>
                  (and
                     (INV_REC_fact__2_PRE n$2_0_old_1)
                     cmp$2_0_1)
                  (INV_REC_fact__2 n$2_0_old_1 result$2_1)))))))
(rule
   (let
      ((n$2_0_1 n$2_0_old_1))
      (let
         ((cmp$2_0_1 (<= n$2_0_1 0)))
         (let
            ((sub$2_0_1 (- n$2_0_1 1)))
            (=>
               (and
                  (INV_REC_fact__2_PRE n$2_0_old_1)
                  (not cmp$2_0_1))
               (INV_REC_fact__2_PRE sub$2_0_1))))))
(rule
   (let
      ((n$2_0_1 n$2_0_old_1))
      (let
         ((cmp$2_0_1 (<= n$2_0_1 0)))
         (let
            ((sub$2_0_1 (- n$2_0_1 1)))
            (let
               ((mul$2_0_1 (* n$2_0_1 call$2_0_1)))
               (let
                  ((retval.0$2_0_1 mul$2_0_1))
                  (let
                     ((result$2_1 retval.0$2_0_1))
                     (=>
                        (and
                           (INV_REC_fact__2_PRE n$2_0_old_1)
                           (not cmp$2_0_1)
                           (INV_REC_fact__2 sub$2_0_1 call$2_0_1))
                        (INV_REC_fact__2 n$2_0_old_1 result$2_1)))))))))
(query
   END_QUERY
   :print-certificate
   true)
