;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname some) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
(Let 'vecinit44356
     (Let '_44354 (If (Let 'tmp44361 (GlobalValue 'free_ptr)
                           (Let 'tmp44362 (Prim '+ (list (Var 'tmp44361) (Int 16)))
                                (Let 'tmp44363 (GlobalValue 'fromspace_end)
                                     (Prim '< (list (Var 'tmp44362) (Var 'tmp44363))))))
                      (Void)
                      (collect 16))
          (Let 'alloc44352 (allocate 1 (Vector Integer))
               (Let '_44353 (Prim 'vector-set! (list (Var 'alloc44352) (Int 0) (Int 2)))
                    (Var 'alloc44352))))
     (Let '_44360 (If (Let 'tmp44364 (GlobalValue 'free_ptr)
                           (Let 'tmp44365 (Prim '+ (list (Var 'tmp44364) (Int 32)))
                                (Let 'tmp44366 (GlobalValue 'fromspace_end)
                                     (Prim '< (list (Var 'tmp44365) (Var 'tmp44366))))))
                      (Void)
                      (collect 32))
          (Let 'alloc44355 (allocate 3 (Vector Integer Boolean (Vector Integer)))
               (Let '_44359 (Prim 'vector-set! (list (Var 'alloc44355) (Int 0) (Int 40)))
                    (Let '_44358 (Prim 'vector-set! (list (Var 'alloc44355) (Int 1) (Bool #t)))
                         (Let '_44357 (Prim 'vector-set! (list (Var 'alloc44355) (Int 2) (Var 'vecinit44356)))
                              (Let 'tmp44367 (Prim 'vector-ref (list (Var 'alloc44355) (Int 2)))
                                   (Prim 'vector-ref (list (Var 'tmp44367) (Int 0))))))))))

(CProgram
 '()
 (list
  (cons 'block44373
        (Seq (collect 16) (Goto 'block44371)))
  (cons 'block44372
        (Seq (Assign (Var '_44354) (Void)) (Goto 'block44371)))
  (cons 'block44371
   (Seq
    (Assign (Var 'alloc44352) (allocate 1 (Vector Integer)))
    (Seq
     (Assign
      (Var '_44353)
      (Prim 'vector-set! (list (Var 'alloc44352) (Int 0) (Int 2))))
     (Seq
      (Assign (Var 'vecinit44356) (Var 'alloc44352))
      (Seq
       (Assign (Var 'tmp44364) (GlobalValue 'free_ptr))
       (Seq
        (Assign (Var 'tmp44365) (Prim '+ (list (Var 'tmp44364) (Int 32))))
        (Seq
         (Assign (Var 'tmp44366) (GlobalValue 'fromspace_end))
         (IfStmt
          (Prim '< (list (Var 'tmp44365) (Var 'tmp44366)))
          (Goto 'block44369)
          (Goto 'block44370)))))))))
  (cons 'block44370 (Seq (collect 32) (Goto 'block44368)))
  (cons 'block44369 (Seq (Assign (Var '_44360) (Void)) (Goto 'block44368)))
  (cons
   'block44368
   (Seq
    (Assign
     (Var 'alloc44355)
     (allocate 3 (Vector Integer Boolean (Vector Integer))))
    (Seq
     (Assign
      (Var '_44359)
      (Prim 'vector-set! (list (Var 'alloc44355) (Int 0) (Int 40))))
     (Seq
      (Assign
       (Var '_44358)
       (Prim 'vector-set! (list (Var 'alloc44355) (Int 1) (Bool #t))))
      (Seq
       (Assign
        (Var '_44357)
        (Prim
         'vector-set!
         (list (Var 'alloc44355) (Int 2) (Var 'vecinit44356))))
       (Seq
        (Assign
         (Var 'tmp44367)
         (Prim 'vector-ref (list (Var 'alloc44355) (Int 2))))
        (Return (Prim 'vector-ref (list (Var 'tmp44367) (Int 0))))))))))
  (cons
   'start
   (Seq
    (Assign (Var 'tmp44361) (GlobalValue 'free_ptr))
    (Seq
     (Assign (Var 'tmp44362) (Prim '+ (list (Var 'tmp44361) (Int 16))))
     (Seq
      (Assign (Var 'tmp44363) (GlobalValue 'fromspace_end))
      (IfStmt
       (Prim '< (list (Var 'tmp44362) (Var 'tmp44363)))
       (Goto 'block44372)
       (Goto 'block44373))))))))

