; Collaborators :
; - Nick Irmscher
; - Marshal Gress

#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "type-check-Lfun.rkt")
(require "interp-Cfun.rkt")
(require "type-check-Cfun.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require graph)
(require "graph-printing.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(require data/queue)
(provide (all-defined-out))

; shrink : Rif -> Rif
(define (shrink p)
  (match p
    [(ProgramDefsExp info ds e)
     (define ds^
       (append (for/list ([d ds])
                 (match d
                   [(Def f inputs type ls e)
                    (Def f inputs type ls (shrink-exp e))]))
               (list (Def 'main '() 'Integer '() (shrink-exp e)))))
     (ProgramDefs info ds^)]))

; shrink-exp : Exp -> Exp
(define (shrink-exp e)
  (match e
    [(Prim 'and `(,e1 ,e2))
     (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
    [(Prim 'or  `(,e1 ,e2))
     (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
    [(HasType `,e `,t)
     (HasType (shrink-exp e) t)]
    [`,atm
     #:when (atm? atm)
     atm]
    [(Apply rator rands)
     (Apply (shrink-exp rator) (map shrink-exp rands))]
    [(Prim op ls)
     (Prim op (map shrink-exp ls))]
    [(Let x e body)
     (Let x (shrink-exp e) (shrink-exp body))]
    [(If cnd thn els)
     (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
    [(SetBang var rhs)
     (SetBang var (shrink-exp rhs))]
    [(Begin es body)
     (Begin (map shrink-exp es) (shrink-exp body))]
    [(WhileLoop cnd body)
     (WhileLoop (shrink-exp cnd) (shrink-exp body))]
    [else (error "shrink-exp does not handle" e)]))     

;; uniquify : R1 -> R1 
(define (uniquify p)
  (match p
    [(ProgramDefs info ds)
     (define top-level
       (foldr (λ (d rest)
                (match d
                  [(Def f inputs type ls e)
                   (cons (cons f (if (eq? f 'main) 'main (gensym f))) rest)]))
              empty ds))
     (define ds^
       (for/list ([d ds])
         (match d
           [(Def f inputs type ls e)
            (define env (map (λ (pair)
                               (match pair
                                 [`(,arg : ,type) (cons arg (gensym arg))])) inputs))
            (define inputs^
              (map (λ (pair)
                     (match pair
                       [`(,arg : ,type) `(,(dict-ref env arg) : ,type)])) inputs))
            (Def (dict-ref top-level f) inputs^ type ls ((uniquify-exp (append top-level env)) e))])))
     (ProgramDefs (dict-set info 'functions (map cdr top-level)) ds^)]))

; uniquify-exp : [Dictionaryof Symbol Symbol] -> [Exp -> Exp]
(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Apply rator rands)
       (Apply ((uniquify-exp env) rator) (map (uniquify-exp env) rands))]
      [(HasType `,e `,t)
       (HasType ((uniquify-exp env) e) t)]
      [`,atm
       #:when (atm? atm)
       atm]
      [(If cnd thn els)
       (If ((uniquify-exp env) cnd) ((uniquify-exp env) thn) ((uniquify-exp env) els))]
      [(Let x e body)
       (define x^ (gensym x))
       (Let x^ ((uniquify-exp env) e) ((uniquify-exp (dict-set env x x^)) body))]
      [(SetBang var rhs)
       (SetBang (dict-ref env var) ((uniquify-exp env) rhs))]
      [(Begin es body)
       (Begin (map (uniquify-exp env) es) ((uniquify-exp env) body))]
      [(WhileLoop cnd body)
       (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [else (error "uniquify-exp does not handle" e)])))

; reveal-functions : LFun -> LFunRef
(define (reveal-functions p)
  (match p
    [(ProgramDefs info ds)
     (define ds^
       (for/list ([d ds])
         (match d
           [(Def f inputs type ls e)
            (Def f inputs type ls ((rf-exp (dict-ref info 'functions)) e))])))
     (ProgramDefs info ds^)]))

; rf-exp : [ListOf Symbol] -> [Exp -> Exp]
(define (rf-exp functions)
  (λ (e)
    (let* ([recur (rf-exp functions)])
      (match e
        [(Var x)
         (if (memq x functions) (FunRef x) (Var x))]
        [(Apply rator rands)
         (Apply (recur rator) (map recur rands))]
        [(HasType `,e `,t)
         (HasType (recur e) t)]
        [`,atm
         #:when (atm? atm)
         atm]
        [(If cnd thn els)
         (If (recur cnd) (recur thn) (recur els))]
        [(Let x e body)
         (Let x (recur e) (recur body))]
        [(SetBang var rhs)
         (SetBang var (recur rhs))]
        [(Begin es body)
         (Begin (map recur es) (recur body))]
        [(WhileLoop cnd body)
         (WhileLoop (recur cnd) (recur body))]
        [(Prim op es)
         (Prim op (for/list ([e es]) (recur e)))]
        [else (error "rf-exp does not handle" e)]))))


; limit-functions : LFunRef -> LFunRef
(define (limit-functions p)
  (match p
    [(ProgramDefs info ds)
     (define ds^
       (for/list ([d ds])
         (match d
           [(Def f inputs type ls e)
            (cond
              [(> (length inputs) 6)
               ;; if more than 6 inputs, compress all inputs from the 6th to be a vector
               (define extra (drop inputs 5))
               (define tup (gensym 'vec-param))
               (define inputs^ (append (take inputs 5)
                                       (list `(,tup : ,(compress extra)))))
               (define (lf-gen-env lopr n)
                 (cond
                   [(empty? lopr) empty]
                   [else (cons
                          (match (first lopr)
                            [`(,var : ,type) (cons var (Prim 'vector-ref (list (Var tup) (Int n))))])
                          (lf-gen-env (rest lopr) (add1 n)))]))
               (define env (lf-gen-env extra 0))
               (Def f inputs^ type ls ((lf-exp env) e))]
              [else
               (Def f inputs type ls ((lf-exp '()) e))])])))
     (ProgramDefs info ds^)]))

; compress: [ListOf [Symbol : Type]] -> Vector
(define (compress lopr)
  (cons 'Vector
        (map (λ (pr)
               (match pr
                 [`(,var : ,type) type])) lopr)))

; lf-exp : Env -> [Exp -> Exp]
(define (lf-exp env)
  (λ (e)
    (define recur (lf-exp env))
    (match e      
      [(Var x)
       (if (dict-has-key? env x) (dict-ref env x) (Var x))]
      [(Apply rator rands)
       (define rands-rec (map recur rands))
       (define rands^
         (cond
           [(<= (length rands-rec) 6) rands-rec]
           [else (append (take rands-rec 5)
                         (list (Prim 'vector (drop rands-rec 5))))]))
       (Apply (recur rator) rands^)]
      [(FunRef f) (FunRef f)] 
      [(HasType `,e `,t)
       (HasType (recur e) t)]
      [`,atm
       #:when (atm? atm)
       atm]
      [(If cnd thn els)
       (If (recur cnd) (recur thn) (recur els))]
      [(Let x e body)
       (Let x (recur e) (recur body))]
      [(SetBang var rhs)
       (SetBang var (recur rhs))]
      [(Begin es body)
       (Begin (map recur es) (recur body))]
      [(WhileLoop cnd body)
       (WhileLoop (recur cnd) (recur body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) (recur e)))]
      [else (error "lf-exp does not handle" e)])))

; expose-allocation : Ltup -> Lalloc
(define (expose-allocation p)
  (match p
    [(ProgramDefs info ds)
     (ProgramDefs info
                  (for/list ([d ds])
                    (match d
                      [(Def f inputs type ls e)
                       (Def f inputs type ls (ea-exp e))])))]))

; ea-exp : Exp(Ltup) -> Exp(Lalloc)
(define (ea-exp e)
  (match e
    [(FunRef f) (FunRef f)]
    [(Apply rator rands)
     (Apply (ea-exp rator) (map ea-exp rands))]
    [(HasType `,e `,t)
     (ea-helper e t)]
    [`,atm
     #:when (atm? atm)
     atm]
    [(If cnd thn els)
     (If (ea-exp cnd) (ea-exp thn) (ea-exp els))]
    [(Let x e body)
     (Let x (ea-exp e) (ea-exp body))]
    [(SetBang var rhs)
     (SetBang var (ea-exp rhs))]
    [(Begin es body)
     (Begin (map ea-exp es) (ea-exp body))]
    [(WhileLoop cnd body)
     (WhileLoop (ea-exp cnd) (ea-exp body))]
    [(Prim op es)
     (Prim op (for/list ([e es]) (ea-exp e)))]
    [else (error "ea-exp does not handle" e)]))

; ea-helper : Exp(Ltup) Type(Ltup) -> Exp(Lalloc)
(define (ea-helper exp type)
  (match exp
    [(Prim 'vector es)
     (define alloc (gensym 'alloc))
     (define len (length es))
     (define dict (map (λ (e) (cons (if (HasType? e) (gensym 'vecinit) 'basic) (ea-exp e))) es)) 
     (define byte (* 8 (+ 1 len)))
     (define vector-set!-helper
       (λ (alloc n dict)
         (cond
           [(empty? dict) (Var alloc)]
           [(cons? dict)
            (Let (gensym '_)
                 (Prim 'vector-set! (list (Var alloc)
                                          (Int n)
                                          (if (eq? 'basic (car (car dict)))
                                              (cdr (car dict))
                                              (Var (car (car dict))))))
                 (vector-set!-helper alloc (add1 n) (cdr dict)))])))
     (define cont (Let (gensym 'collectret)
                       (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int byte)))
                                          (GlobalValue 'fromspace_end)))
                           (Void)
                           (Collect byte))
                       (Let alloc
                            (Allocate len type)
                            (vector-set!-helper alloc 0 dict))))
     (foldr
      (λ (pair rest) (Let (car pair) (cdr pair) rest)) cont
      (filter (λ (pr) (not (eq? 'basic (car pr)))) dict))]
    [else
     (error "A non-tuple is passed into ea-helper " exp)]))

; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info ds)
     (ProgramDefs info
                  (for/list ([d ds])
                    (match d
                      [(Def f inputs type ls e)
                       (Def f inputs type ls (rco-exp e))])))]))

; rco-exp : Exp -> Exp
(define (rco-exp e)
  (match e
    [`,atm
     #:when (atm? atm)
     atm]
    [(Apply rator rands)
     (define rator^ (rco-atom rator))
     (define lopr (map rco-atom rands))
     (define rands^ (map car lopr))
     (define dict (append (cdr rator^) (foldr (λ (pr l) (append (cdr pr) l)) '() lopr)))
     (update (Apply (car rator^) rands^) dict)]
    [(FunRef f) (FunRef f)]
    [(Collect i) (Collect i)]
    [(Allocate int type) (Allocate int type)]
    [(GlobalValue var) (GlobalValue var)] 
    [(SetBang var rhs)
     (SetBang var (rco-exp rhs))]
    [(Begin es body)
     (Begin (map rco-exp es) (rco-exp body))]
    [(WhileLoop cnd body)
     (WhileLoop (rco-exp cnd) (rco-exp body))]
    [(Let x e body)
     (Let x (rco-exp e) (rco-exp body))]
    [(If cnd thn els)
     (If (rco-exp cnd) (rco-exp thn) (rco-exp els))]
    [(Prim op es)
     (define lod (map rco-atom es))
     (define newes (map car lod))
     (define dict (foldr (λ (pr l) (append (cdr pr) l)) '() lod))
     (update (Prim op newes) dict)]
    [else (error "rco-exp does not handle " e)]))

; rco-atom : Exp -> (list Atom [DictionaryOf Symbol Exp])
(define (rco-atom e)
  (match e
    [`,atm
     #:when (atm? atm)
     (cons atm '())]
    [(Apply rator rands)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define rator^ (rco-atom rator))
     (define lopr (map rco-atom rands))
     (define rands^ (map car lopr))
     (define dict (append (cdr rator^) (foldr (λ (pr l) (append (cdr pr) l)) '() lopr)))
     (define value (Apply (car rator^) rands^))
     (define alist (dict-set dict key value))
     (cons atm alist)]
    [(FunRef f)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (FunRef f))
     (define alist (dict-set '() key value))
     (cons atm alist)]
    [(Collect i)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (Collect i))
     (define alist (dict-set '() key value))
     (cons atm alist)]
    [(Allocate int type)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (Allocate int type))
     (define alist (dict-set '() key value))
     (cons atm alist)]
    [(GlobalValue var)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (GlobalValue var))
     (define alist (dict-set '() key value))
     (cons atm alist)] 
    [(Begin es body)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (Begin (map rco-exp es) (rco-exp body)))
     (define alist (dict-set '() key value))
     (cons atm alist)]
    [(SetBang var rhs)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (SetBang var (rco-exp rhs)))
     (define alist (dict-set '() key value))
     (cons atm alist)]
    [(WhileLoop cnd body)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (WhileLoop (rco-exp cnd) (rco-exp body)))
     (define alist (dict-set '() key value))
     (cons atm alist)]
    [(If cnd thn els)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (If (rco-exp cnd) (rco-exp thn) (rco-exp els)))
     (define alist (dict-set '() key value))
     (cons atm alist)]
    [(Let x e body)
     (define key (gensym 'tmp))
     (define newe (rco-exp e))
     (define newbody (rco-exp body))
     (define atm (if (atm? newbody) newbody (Var key)))
     (define alist (if (atm? newbody) (dict-set '() x newe)
                       (dict-set (dict-set '() x newe) key newbody)))
     (cons atm alist)]
    [(Prim op es)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define lod (map rco-atom es))
     (define es^ (map car lod))
     (define dict (foldr (λ (pr l) (append (cdr pr) l)) '() lod))
     (define value (Prim op es^))
     (define alist (dict-set dict key value))
     (cons atm alist)]))


(define (update e dict)
  (cond
    [(dict-empty? dict) e]
    [else (let* ([x (car (car dict))]
                 [v (cdr (car dict))]
                 [body (update e (cdr dict))])
            (Let x v body))]))

;; explicate-control : R1 -> C0
(define blocks (make-hash))
(define (explicate-control p)
  (match p
    [(ProgramDefs info ds)
     (ProgramDefs info (for/list ([d ds]) (explicate-define d)))]))

; explicate-define : def(L) -> def(C)
(define explicate-define
  (λ (d)
    (match d
      [(Def f inputs type ls e)
       (dict-clear! blocks)
       (define bodyctail (explicate-tail e))
       (dict-set! blocks (string->symbol (string-append (symbol->string f) "start")) bodyctail)
       (Def f inputs type ls (hash->list blocks))])))
    
; explicate-pred : Exp(Rif) Tail(Cif) Tail(Cif) -> Tail(Cif) 
(define (explicate-pred cnd thn els)
  (match cnd
    [(Apply rator rands)
     (define tmp (gensym 'tmp))
     (explicate-assign
      cnd tmp
      (IfStmt (Prim 'eq? (list (Var tmp) (Bool #t)))
              (create-block thn)
              (create-block els)))]
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t)))
                     (create-block thn)
                     (create-block els))]
    [(Begin (list) body)
     (explicate-pred body thn els)]
    [(Begin (cons exp exp*) body)
     (explicate-effect exp (explicate-pred (Begin exp* body) thn els))]
    [(Let x rhs body)
     (define cont (explicate-pred body thn els))
     (explicate-assign rhs x cont)]
    [(Prim 'not (list e)) (explicate-pred e els thn)]
    [(Prim op es) #:when (or (eq? op 'eq?) (eq? op '<)
                             (eq? op '>) (eq? op '>=)
                             (eq? op '<=) (eq? op 'vector-ref))
                  (IfStmt (Prim op es) (create-block thn)
                          (create-block els))]
    [(Bool b) (if b thn els)]
    [(If cnd^ thn^ els^)
     (define thn-block (create-block thn))
     (define els-block (create-block els))
     (explicate-pred cnd^
                     (explicate-pred thn^ thn-block els-block)
                     (explicate-pred els^ thn-block els-block))]
    [else (error "explicate_pred unhandled case" cnd)]))

; explicate-tail : Exp(Rif) -> Tail(Cif)
(define (explicate-tail e)
  (match e
    [`,atm
     #:when (atm? atm)
     (Return atm)]
    [(Apply rator rands) (TailCall rator rands)]
    [(FunRef f) (Return (FunRef f))]
    [(Allocate int type) (Return (Allocate int type))]
    [(GlobalValue var) (Return (GlobalValue var))]
    [(If cnd thn els)
     (define thn^ (explicate-tail thn))
     (define els^ (explicate-tail els))
     (explicate-pred cnd thn^ els^)]
    [(Let x rhs body)
     (define bodyctail (explicate-tail body))
     (explicate-assign rhs x bodyctail)]
    [(Prim op es)
     (Return (Prim op es))]
    [(Begin es body)
     (foldl (λ (exp cont)
              (explicate-effect exp cont))
            (explicate-tail body) es)]
    [(SetBang var exp)
     (explicate-effect (SetBang var exp) (explicate-tail (Void)))]
    [(WhileLoop cnd body)
     (explicate-effect (WhileLoop cnd body) (explicate-tail (Void)))]
    [else (error "explicate_tail unhandled case " e)]))

; explicate-assign : Exp(Rif) Symbol Tail(Cif) -> Tail(Cif)
(define (explicate-assign e x cont)
  (match e
    [(Apply rator rands)
     (Seq (Assign (Var x) (Call rator rands)) cont)]
    [(FunRef f)
     (Seq (Assign (Var x) (FunRef f)) cont)]
    [`,atm
     #:when (atm? atm)
     (Seq (Assign (Var x) atm) cont)]
    [(Collect int) (Seq (Collect int) cont)]
    [(Allocate int type) (Seq (Assign (Var x) (Allocate int type)) cont)]
    [(GlobalValue var) (Seq (Assign (Var x) (GlobalValue var)) cont)]
    [(If cnd thn els)
     (define cont^ (create-block cont)) ; (Goto label)
     (define thn^ (explicate-assign thn x cont^)) ; Tail(Cif) 
     (define els^ (explicate-assign els x cont^)) ; Tail(Cif)
     (explicate-pred cnd thn^ els^)]
    [(Let s rhs body)
     (define bodyctail (explicate-assign body x cont))
     (explicate-assign rhs s bodyctail)]
    [(Prim op es)
     (Seq (Assign (Var x) (Prim op es)) cont)]
    [(Begin es body)
     (foldl (λ (exp cont)
              (explicate-effect exp cont))
            (explicate-assign body x cont) es)]
    [(SetBang var exp)
     (explicate-effect (SetBang var exp) (explicate-assign (Void) x cont))]
    [(WhileLoop cnd body)
     (explicate-effect (WhileLoop cnd body) (explicate-assign (Void) x cont))]
    [else (error "explicate-assign unhandled case" e)]))

; explicate-effect : Exp(R) Tail(C) -> Tail(C)
(define (explicate-effect e cont)
  (match e
    [(Prim op ls)
     #:when (or (eq? op 'read)
                (eq? op 'vector-set!))
     (Seq e cont)]
    [(Collect int) (Seq e cont)]
    [(Let s rhs body)
     (define bodyctail (explicate-effect body cont))
     (explicate-assign rhs s bodyctail)]
    [(Begin es body)
     (foldl (λ (exp cont)
              (explicate-effect exp cont))
            (explicate-effect body cont) es)] 
    [(SetBang var exp)
     (explicate-assign exp var cont)]
    [(WhileLoop cnd body)
     (define loop (gensym 'loop_))
     (define cont^ (Goto loop)) 
     (define body^ (explicate-effect body cont^))
     (dict-set! blocks loop (explicate-pred cnd body^ cont))
     cont^]
    [else cont]))

; create-block : Tail(Cif) -> (Goto label)
; dict-set! the input tail and return a goto to this tail
(define (create-block t)
  (match t
    [_ (define key (gensym 'block_))
       (dict-set! blocks key t)
       (Goto key)]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match-let
      ([(ProgramDefs info ds) (type-check-Cfun p)])
    (define ds^
      (for/list ([d ds])
         (match d
           [(Def f inputs type ls e)
            (set-box! func-name (symbol->string f))
            ;; initialize parameters using the registers
            (define inputs^
                  (for/list ([input inputs])
                    (match input
                      [`(,arg : ,type) (Var arg)])))
            (define reg-to-param (assign-params-to-regs (take callq-param (length inputs)) inputs^))
             
            (define e^
              (for/list ([pair e])
                (define label (car pair))
                (define tail  (cdr pair))
                (define instrs
                  (if (eq? label (string->symbol (string-append (unbox func-name) "start")))
                      (append reg-to-param (si-tail tail))
                      (si-tail tail)))
                (cons label (Block '() instrs))))
            (Def f empty type (dict-set ls 'num-params (length inputs)) e^)])))
    (ProgramDefs info ds^)))

(define func-name (box "nothing"))
; si-tail : tail -> [ListOf Instr]
(define si-tail
  (λ (tail)
    (match tail
      [(TailCall rator rands)
       (let* ([rator (si-atm rator)]
              [rands (map si-atm rands)])
         (append (assign-params-to-regs rands callq-param)
                 (list (TailJmp rator (length rands)))))]
      [(Return exp)
       (define instrs (si-exp exp (Reg 'rax)))
       (append instrs
               (list (Jmp (string->symbol (string-append (unbox func-name) "conclusion")))))]
      [(Seq stmt tail)
       (append (si-stmt stmt)
               (si-tail tail))]
      [(Goto label) (list (Jmp label))]
      [(IfStmt cnd (Goto thn) (Goto els))
       (match cnd
         [(Prim cmp `(,atm1 ,atm2))
          (list (Instr 'cmpq (list (si-atm atm2) (si-atm atm1)))
                (JmpIf
                 (cond
                   [(equal? cmp 'eq?) 'e]
                   [(equal? cmp '<) 'l]
                   [(equal? cmp '<=) 'le]
                   [(equal? cmp '>) 'g]
                   [(equal? cmp '>=) 'ge]
                   [else (error "jmpif")])
                 thn)
                (Jmp els))])]
      [else (error "expected a tail for si-tail, instead got" tail)])))

; si-atm : atm -> arg
(define si-atm
  (λ (atm)
    (match atm
      [(Int n) (Imm n)]
      [(Var x) (Var x)]
      [(Bool b) (match b
                  [#t (Imm 1)]
                  [#f (Imm 0)])]
      [(Void) (Imm 0)]
      [else (error "expected an atom for si-atm, instead got" atm)])))

; type->mask : [ListOf type] -> Integer
(define (type->mask lot)
  (binary-to-decimal (reverse (map (λ (t) (if (vec? t) 1 0)) lot))))

; binary-to-decimal : [ListOf BinaryNumber] -> Integer
(define binary-to-decimal
  (λ (lob)
    (cond
      [(empty? lob) 0]
      [(cons? lob)
       (if (zero? (car lob))
           (binary-to-decimal (cdr lob))
           (+ (expt 2 (length (rest lob)))
              (binary-to-decimal (cdr lob))))])))

; vec? : type -> Boolean
(define vec?
  (λ (t)
    (match t
      [(cons 'Vector `,ls) true]
      [else false])))

; assign-params-to-regs : [ListOf Arg] [ListOf Arg]-> [ListOf (Instr 'movq (list Arg Arg))]
(define (assign-params-to-regs loa loe)
  (cond
    [(empty? loa) empty]
    [else (cons (Instr 'movq (list (car loa) (car loe)))
                (assign-params-to-regs (cdr loa) (cdr loe)))]))

; si-exp : Exp x86Arg -> [ListOf Instr]
(define si-exp
  (λ (exp arg)
    (match exp
      [(FunRef f)
       (list (Instr 'leaq (list (FunRef f) arg)))]
      [(Call rator rands)
       (let* ([rator (si-atm rator)]
              [rands (map si-atm rands)])
         (append (assign-params-to-regs rands callq-param)
                 (list (IndirectCallq rator (length rands))
                       (Instr 'movq (list (Reg 'rax) arg)))))]
      [`,atm
       #:when (atm? atm)
       (list (Instr 'movq (list (si-atm atm) arg)))]
      [(Prim 'not `(,atm))
       (define arg1 (si-atm atm))
       (match arg1
         [(Var x)
          #:when (equal? arg1 arg)
          (list (Instr 'xorq (list (Imm 0) arg)))]
         [else (list (Instr 'movq (list arg1 arg))
                     (Instr 'xorq (list (Imm 1) arg)))])]
      [(Allocate `,len `,type)
       (define tag (Imm (+ (arithmetic-shift (type->mask (cdr type)) 7)
                           (arithmetic-shift len 1) 1)))
       (list (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
             (Instr 'addq (list (Imm (* 8 (+ len 1))) (Global 'free_ptr)))
             (Instr 'movq (list tag (Deref 'r11 0)))
             (Instr 'movq (list (Reg 'r11) arg)))]
      [(GlobalValue var)
       (list (Instr 'movq (list (Global var) arg)))]
      [(Prim 'vector-ref `(,tup ,n))
       (list (Instr 'movq (list tup (Reg 'r11)))
             (Instr 'movq (list (Deref 'r11 (* 8 (add1 (Int-value n)))) arg)))]
      [(Prim 'vector-set! `(,tup ,n ,rhs))
       (list (Instr 'movq (list tup (Reg 'r11)))
             (Instr 'movq (list (si-atm rhs) (Deref 'r11 (* 8 (add1 (Int-value n))))))
             (Instr 'movq (list (Imm 0) arg)))]
      [(Prim op `(,atm1 ,atm2))
       #:when (or (equal? op '+) (equal? op '-))
       (define arg1 (si-atm atm1))
       (define arg2 (si-atm atm2))
       (define instr (if (equal? '+ op) 'addq 'subq))
       (abstraction instr arg arg1 arg2)]
      [(Prim '- `(,atm1)) (list (Instr 'movq (list (si-atm atm1) arg))
                                (Instr 'negq (list arg)))]
      [(Prim cmp `(,atm1 ,atm2))
       #:when (or (equal? 'eq? cmp) (equal? '< cmp) (equal? '<= cmp) (equal? '> cmp) (equal? '>= cmp))
       (define arg1 (si-atm atm1))
       (define arg2 (si-atm atm2))
       (append (cmp-to-instrs cmp arg1 arg2)
               (list (Instr 'movzbq (list (ByteReg 'al) arg))))]
      [(Prim 'read ls) (list (Callq 'read_int 0)
                             (Instr 'movq (list (Reg 'rax) arg)))])))

; abstraction : Symbol(op) -> [ListOf Instrs]
(define (abstraction op arg arg1 arg2)
  (cond
    [(equal? arg arg2) (list (Instr op (list arg1 arg2)))]
    [(equal? arg arg1) (list (Instr op (list arg2 arg1)))]
    [else 
     (list (Instr 'movq (list arg1 arg))
           (Instr op (list arg2 arg)))]))

; si-stmt : stmt -> [ListOf Instr]
(define (si-stmt stmt)
  (match stmt
    [(Assign (Var var) exp)
     (si-exp exp (Var var))]
    [(Prim 'read ls)
     (list (Callq 'read_int 0))]
    [(Prim 'vector-set! `(,tup ,n ,rhs))
     (list (Instr 'movq (list tup (Reg 'r11)))
           (Instr 'movq (list rhs (Deref 'r11 (* 8 (add1 (Int-value n)))))))]
    [(Collect bytes)
     (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
           (Instr 'movq (list (Imm bytes) (Reg 'rsi)))
           (Callq 'collect 2))]))

; cmp-to-instrs : Symbol Arg(x86Var) Arg(x86Arg) -> [ListOf Instr](cmpq and sete, movzbq handled in the si-stmt)
(define (cmp-to-instrs cmp arg1 arg2)
  (list (Instr 'cmpq (list arg2 arg1))
        (Instr 'set (list (match cmp
                            ['eq? 'e]
                            ['< 'l]
                            ['<= 'le]
                            ['> 'g]
                            ['>= 'ge])
                          (ByteReg 'al)))))

(define label->live (make-hash)) ;; needs to be global because we use them in read and write

; analyze_dataflow :
; Set up the global variable, label->live, correctly
(define (analyze_dataflow G transfer bottom join)
  (for ([v (in-vertices G)])
    (dict-set! label->live v bottom))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
         (define node (dequeue! worklist))
         (define input (for/fold ([state bottom])
                                 ([pred (in-neighbors trans-G node)])
                         (join state (dict-ref label->live pred))))
         (define output (transfer node input))
         (cond [(not (equal? output (dict-ref label->live node)))
                (dict-set! label->live node output)
                (for ([v (in-neighbors G node)])
                  (enqueue! worklist v))])))

; transfer : [ListOf Instrs] [SetOf Location] -> [SetOf Location]
(define (transfer-helper loi input)
  (cond
    [(empty? loi) input]
    [else (let ([liveafterset (transfer-helper (cdr loi) input)])
            (set-union (set-subtract liveafterset (written (car loi)))
                       (read (car loi))))]))

;; uncover-live : pseudo-x86 -> pseudo-x86
(define (uncover-live p)
  (match p
    [(ProgramDefs info ds)
     (define ds^ (for/list ([d ds])
                   (uncover-live-def d)))
     (ProgramDefs info ds^)]))


; uncover-live : def(pseudo-x86) -> def(pseudo-x86)
(define (uncover-live-def d)
  (match d
    [(Def f inputs type ls labels-blocks)
     (hash-clear! label->live) ;; clean up the global variable
     (define conclusion (string->symbol (string-append (symbol->string f) "conclusion")))
     (dict-set! label->live conclusion (set (Reg 'rax) (Reg 'rsp)))
     (define edge-list (create-edges labels-blocks)) ;; create all edges
     (define graph (make-multigraph edge-list)) ;; create the graph from the edges
     (for/list ([pair labels-blocks])
       (add-vertex! graph (car pair)))
     (remove-vertex! graph conclusion)
     (define (trans block-label live-after)
       (match (dict-ref labels-blocks block-label)
         [(Block binfo instrs)
          (transfer-helper instrs live-after)]))
     (analyze_dataflow graph trans (set) set-union)          
     (define blocks^ (sequence->list (in-vertices graph))) ; [ListOf Label] without 'conclusion
     (define newblocks
       (for/list ([label blocks^])
         (match (dict-ref labels-blocks label)
           [(Block binfo instrs)
            (cons label (Block (dict-set binfo 'lives (ul-instrs instrs)) instrs))])))
     (Def f inputs type ls newblocks)]))

; create-edges : [DictionaryOf Label Block] -> [ListOf Edge]
; Create an edge pointing from a to b if block a has a jmp or jmpif to block b
(define (create-edges blocks)
  (foldr (λ (pair rest)
           (let ([current-edges (match (cdr pair)
                                  [(Block binfo instrs)
                                   (create-edges-helper (car pair) instrs)])])
             (append current-edges rest)))
         '() blocks))

; create-edges-helper : Label [ListOf Instr] -> [ListOf Edge]
; Create an edge pointing from the given label to b if the given [ListOf Instr] has a jmp or a jmpif to block b
(define (create-edges-helper label loi)
  (cond
    [(empty? loi) empty]
    [(cons? loi) (let* ([rest (create-edges-helper label (rest loi))])
                   (match (first loi)
                     [(Jmp destination) (cons (list label destination) rest)]
                     [(JmpIf cc destination) (cons (list label destination) rest)]
                     [_ rest]))]))


; ul-instrs : [ListOf Instr] -> [ListOf [SetOf Location]]
(define (ul-instrs loi)
  (cond
    [(empty? loi) (list (set))]
    [else (let* ([nlist (ul-instrs (cdr loi))]
                 [nafter (car nlist)]
                 [curset (set-union (set-subtract nafter (written (car loi)))
                                    (read (car loi)))])
            (cons curset nlist))]))

; written : Instr -> [SetOf Location]
(define (written i)
  (match i
    [(IndirectCallq arg int)
     (set (Reg 'rax) (Reg 'rdx) (Reg 'rcx)
          (Reg 'rsi) (Reg 'rdi) (Reg 'r8)
          (Reg 'r9)  (Reg 'r10) (Reg 'r11))]
    [(TailJmp arg int)
     (set (Reg 'rax) (Reg 'rdx) (Reg 'rcx)
          (Reg 'rsi) (Reg 'rdi) (Reg 'r8)
          (Reg 'r9)  (Reg 'r10) (Reg 'r11))]
    [(Instr 'negq `(,arg1)) (loc-in-arg arg1)]
    [(Instr 'set `(,cc ,arg1)) (loc-in-arg arg1)]
    [(Callq label int)
     (set (Reg 'rax) (Reg 'rdx) (Reg 'rcx)
          (Reg 'rsi) (Reg 'rdi) (Reg 'r8)
          (Reg 'r9)  (Reg 'r10) (Reg 'r11))]
    [(Instr op `(,arg1 ,arg2))
     #:when (equal? op 'cmpq)
     (set)]
    [(Instr op `(,arg1 ,arg2))
     #:when (or (equal? op 'addq)
                (equal? op 'movq)
                (equal? op 'subq)
                (equal? op 'xorq)
                (equal? op 'leaq))
     (loc-in-arg arg2)]
    [(Instr 'movzbq `(,arg1 ,arg2))
     (set (Reg 'rax))]
    [else (set)]))

; read : Instr -> [Setof Location]
(define (read i)
  (match i
    [(IndirectCallq arg int)
     (set-union (callq-parameters callq-param int)
                (loc-in-arg arg))]
    [(TailJmp arg int)
     (set-union (callq-parameters callq-param int)
                (loc-in-arg arg))]
    [(Instr op `(,arg1 ,arg2))
     #:when (or (equal? op 'movq)
                (equal? op 'movzbq)
                (equal? op 'leaq))
     (loc-in-arg arg1)]
    [(Instr op `(,arg1 ,arg2))
     #:when (or (equal? op 'addq)
                (equal? op 'cmpq)
                (equal? op 'subq)
                (equal? op 'xorq))
     (set-union (loc-in-arg arg1) (loc-in-arg arg2))]
    [(Instr 'negq `(,arg1)) (loc-in-arg arg1)]
    [(Instr 'set `(,cc ,arg1)) (set)]
    [(Callq label `,int)
     (callq-parameters callq-param int)]
    [(Jmp label) (dict-ref label->live label)]
    [(JmpIf cc label) (dict-ref label->live label)]
    [else (error "read does not handle" i)]))

(define callq-param (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9))) 
; callq-parameters : [ListOf Var/Reg] Number -> [SetOf Var/Reg]
(define (callq-parameters ls n)
  (cond
    [(zero? n) (set)]
    [else (set-union (set (car ls))
                     (callq-parameters (cdr ls) (sub1 n)))]))

; loc-in-arg : Arg -> [SetOf Location]
(define (loc-in-arg arg)
  (match arg
    [(Reg reg) (set (Reg reg))]
    [(Var var) (set (Var var))]
    [else (set)]))

; build-interference : pseudo-x86 -> pseudo-x86
(define (build-interference p)
  (match p
    [(ProgramDefs info ds)
     (define ds^ (for/list ([d ds])
                   (build-interference-def d)))
     (ProgramDefs empty ds^)]))
     

;; build-interference : pseudo-x86 -> pseudo-x86
(define (build-interference-def d)
  (match d
    [(Def f inputs type info blocks)
     (define types (dict-ref info 'locals-types)) ;; [DictionaryOf Symbol type]
     (define locals (map car types)) ;; [ListOf Symbol]
     (define edges
       (foldr (λ (pair rest)
                (append
                 (match (cdr pair)
                   [(Block binfo instructions)
                    (bi instructions (cdr (dict-ref binfo 'lives)) types)])
                 rest))
              '() blocks))
     (define graph (undirected-graph edges))
     (for/list ([local locals])
       (add-vertex! graph (Var local)))
     (define info-remove-label-live (dict-remove info 'label->live))
     (define newblocks ;; remove-liveness in info
       (for/list ([pair blocks])
         (cons (car pair)  (match (cdr pair)
                             [(Block binfo instrs)
                              (Block '() instrs)]))))
     (Def f inputs type (dict-set info-remove-label-live 'conflict graph) newblocks)
     #;(X86Program (dict-set info-remove-label-live 'conflict graph) newblocks)]))

;; bi : [ListOf Instructions] [ListOf [SetOf Location]] -> [ListOf Edge]
(define (bi loi los types)
  (cond
    [(empty? loi) empty]
    [else
     (append
      (match (car loi)
        [(TailJmp arg int)
         (define vec-variables
           (filter (λ (var) (vec? (dict-ref types (Var-name var))))
                   (filter Var? (set->list (car los)))))
         (append (foldr (λ (reg rest) (append (map (λ (loc) (list reg loc)) (set->list (car los))) rest)) '()
                        available-caller)
                 (foldr (λ (reg rest) (append (map (λ (loc) (list reg loc)) vec-variables) rest)) '()
                            available-callee) 
                     empty)]
        [(IndirectCallq arg int)
         (define vec-variables
           (filter (λ (var) (vec? (dict-ref types (Var-name var))))
                   (filter Var? (set->list (car los)))))
         (append (foldr (λ (reg rest) (append (map (λ (loc) (list reg loc)) (set->list (car los))) rest)) '()
                        available-caller)
                 (foldr (λ (reg rest) (append (map (λ (loc) (list reg loc)) vec-variables) rest)) '()
                            available-callee) 
                 empty)]
        [(Call label int)
         (define vec-variables
           (filter (λ (var) (vec? (dict-ref types (Var-name var))))
                   (filter Var? (set->list (car los)))))
         ;; if a variable is call-live after a callq, it should not be assigned into any of the
         ;; caller-saved registers to prevent from being polluted
         ;; if this variable happens to be a vector, it should be spilled to r15 later. So, it should
         ;; also not be assigned into any of the callee-saved registers
         (append (foldr (λ (reg rest) (append (map (λ (loc) (list reg loc)) (set->list (car los))) rest)) '()
                        available-caller)
                 (if (eq? label 'collect)
                     (foldr (λ (reg rest) (append (map (λ (loc) (list reg loc)) vec-variables) rest)) '()
                            available-callee) 
                     empty))]
        [else
         (filter (λ (e) (not (equal? 0 e)))
                 (map (λ (loc) (bi-single (car loi) loc))
                      (set->list (car los))))])
      (bi (cdr loi) (cdr los) types))]))

; A [Maybe Edge] is one of:
; - Edge
; - zero

; bi-single : Instruction Location -> [Maybe Edge]
(define bi-single
  (λ (i loc)
    (match i
      [(Instr 'negq `(,arg1))
       (let ([notTarget (not (equal? loc arg1))])
         (cond
           [notTarget (list loc arg1)]
           [else 0]))]
      [(Instr 'set `(,cc ,arg1))
       (let ([notTarget (not (equal? loc arg1))])
         (cond
           [notTarget (list loc arg1)]
           [else 0]))]
      ;; for every caller-saved register, create an edge between the register
      ;; and the given location unless they are the same. create an edge between
      ;; every pair of differernt caller-saved registers. Is this right?? yes!!!
      [(Instr op `(,arg1 ,arg2))
       #:when (equal? op 'cmpq)
       0]
      [(Instr op `(,arg1 ,arg2))
       #:when (or (eq? op 'movq)
                  (eq? op 'leaq))
       (let ([notSource (not (equal? loc arg1))]
             [notTarget (not (equal? loc arg2))])
         (cond
           [(and notSource notTarget)
            (list loc arg2)]
           [else 0]))]
      [(Instr 'movzbq `(,arg1 ,arg2))
       (let ([notSource (not (equal? loc (Reg 'rax)))]
             [notTarget (not (equal? loc arg2))])
         (cond
           [(and notSource notTarget)
            (list loc arg2)]
           [else 0]))]
      [(Instr op `(,arg1 ,arg2))
       #:when (or (equal? op 'addq)
                  (equal? op 'subq)
                  (equal? op 'xorq))
       (let ([notTarget (not (equal? loc arg2))])
         (cond
           [notTarget (list loc arg2)]
           [else 0]))]
      [else 0])))

; pre-coloring : [ListOf Register] Number -> [DictionaryOf Register Number(Color)]
; give a color (n, n+1, n+2, ...) to each register in the given list
(define pre-coloring
  (λ (loreg n)
    (cond
      [(empty? loreg) empty]
      [else (dict-set (pre-coloring (cdr loreg) (add1 n)) (car loreg) n)])))

(define available-caller
  (list (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10)))

(define available-callee
  (list (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))

; init-satur-list : Var Graph [DictionaryOf Reg Number(Color)] -> [SetOf Color]
(define (init-satur-list var g dict)
  (foldr (λ (pair rest)
           (cond
             [(list? (member (car pair) (sequence->list (in-neighbors g var))))
              (set-union (set (cdr pair)) rest)]
             [else rest])) (set) dict))

(define pre-color (append
                   (list (cons (Reg 'rax) -1)
                         (cons (Reg 'rsp) -2)
                         (cons (Reg 'r11) -3)
                         (cons (Reg 'r15) -4)
                         (cons (Global 'free_ptr) -5)
                         (cons (Global 'fromspace_end) -6))
                   (pre-coloring available-caller 0)
                   (pre-coloring available-callee (length available-caller))))

; allocate-registers : pseudo-x86 -> pseudo-x86
(define (allocate-registers p)
  (match p
    [(ProgramDefs info ds)
     (define ds^ (for/list ([d ds])
                   (allocate-registers-def d)))
     (ProgramDefs info ds^)]))

;; allocate-registers-def : def(pseudo-x86) -> def(pseudo-x86)
(define (allocate-registers-def p)
  (match p
    [(Def f inputs type info blocks)
     (define types (dict-ref info 'locals-types))
     (define graph (dict-ref info 'conflict))
     (define color-mapping (ar-vars graph types)) ; [DictionaryOf Var/Reg Number(Color)]
     (define var-mapping (color-to-location color-mapping)) ; [DictionaryOf Var Reg/Deref]
     (define used-callee (filter available-callee? (set->list (list->set (map cdr var-mapping))))) ; [ListOf Reg]
     (define var-mapping^ (map (λ (pr)
                                 (let ([loc (cdr pr)])
                                   (cond
                                     [(Deref? loc)
                                      (cons (car pr)
                                            (Deref (Deref-reg loc)
                                                   (cond
                                                     [(eq? 'rbp (Deref-reg loc)) (- (Deref-offset loc) (* 8 (length used-callee)))]
                                                     [else (Deref-offset loc)])))]
                                     [else pr]))) var-mapping))
     (define num-spill (num-normal-spilled (set->list (list->set (map cdr var-mapping)))))
     (define num-root-spill (num-root-spilled (set->list (list->set (map cdr var-mapping)))))
     (define info^ (list
                    (cons 'num-root-spills num-root-spill)
                    (cons 'num-spill num-spill)
                    (cons 'used-callee used-callee)
                    (cons 'home var-mapping^)
                    (cons 'color (append pre-color color-mapping))
                    (cons 'num-params (dict-ref info 'num-params))))
     (define newblocks
       (for/list ([pair blocks])
         (define label (car pair))
         (define block (cdr pair))
         (define new-instrs
           (match block
             [(Block binfo instrs)
              (assign-homes-instrs instrs var-mapping^)]))
         (cons label (Block '() new-instrs))))
     (Def f inputs type info^ newblocks)]))

; An Arg is one of :
; - (Reg Symbol) ;; Register
; - (Var Symbol) ;; Var
; - (Imm Number) ;; Imm

; ar-graph : Graph -> [DictionaryOf Var Number(Color)]
(define ar-vars ;; change [ListOf Color] to [SetOf Color] later
  (λ (g types)
    (let* ([var-satur-list (make-hash)] ;; [DictionaryOf Var [SetOf Color]]
           [var-handle-list (make-hash)];; [DictionaryOf Var Handle]
           [ls (sequence->list (in-vertices g))]
           [lovar (filter Var? ls)]) 
      (begin
        (for/list ([loc ls]) ;; initialize var-satur-list
          (dict-set! var-satur-list loc (init-satur-list loc g pre-color)))
        (define pq              ;; initialize pq
          (make-pqueue (λ (n1 n2) (> (set-count (dict-ref var-satur-list n1))
                                     (set-count (dict-ref var-satur-list n2))))))
        (for/list ([var lovar]) ;; initialize var-handle-list
          (dict-set! var-handle-list var (pqueue-push! pq var)))
        ;; var-handle-list and var-satur-list and pq working properly at this point!!!

        ; find-index : [SetOf Number] Number (or 10 11) -> Number
        ; if indicator is 11, then assign color to a variable of normal type
        ; if indicator is 10, then assign color to a variable of Vec type
        (define (find-index son n indicator)
          (cond
            [(< n indicator)
             (cond
               [(not (ormap (λ (num) (= num n)) (set->list son))) n]
               [else (find-index son (add1 n) indicator)])]
            [else
             (cond
               [(not (ormap (λ (num) (= num n)) (set->list son))) n]
               [else (find-index son (+ 2 n) indicator)])]))
        (letrec ([ar-ls ;; ar-ls : -> [DictionaryOf Number Var]
                  (λ ()
                    (cond
                      [(zero? (pqueue-count pq)) empty]
                      [else
                       (begin
                         (define var (pqueue-pop! pq))
                         (define type (dict-ref types (Var-name var)))
                         (pqueue-decrease-key! pq (dict-ref var-handle-list var))
                         (define sat-set (dict-ref var-satur-list var)) ;; [SetOf Color(Number)]
                         (define index (if (vec? type)
                                           (find-index sat-set 0 10)
                                           (find-index sat-set 0 11)))
                         (for/list ([neighbor (sequence->list (in-neighbors g var))])
                           (dict-set! var-satur-list neighbor (set-union (set index) (dict-ref var-satur-list neighbor)))) 
                         (define dict-rest (ar-ls))
                         (dict-set dict-rest var index))]))])
          (ar-ls))))))

(define available-callee?
  (λ (r)
    (or (equal? (Reg 'rbx) r)
        (equal? (Reg 'r12) r)
        (equal? (Reg 'r13) r)
        (equal? (Reg 'r14) r)
        (equal? (Reg 'r15) r))))

; color-to-location : [ListOf [PairOf Var Number]] -> [DictionaryOf Arg Location]
(define (color-to-location var-color-list)
  (cond
    [(empty? var-color-list) empty]
    [else (dict-set (color-to-location (cdr var-color-list))
                    (car (car var-color-list))
                    (map-to-loc (car var-color-list)))]))

; A Location is one of:
; - (Reg reg)
; - (Deref reg int)

; map-to-loc : [PairOf Var Number] Number -> Location
(define (map-to-loc pr)
  (let* ([var (car pr)]
         [n (cdr pr)])
    (cond
      [(< n (+ (length available-caller)
               (length available-callee)))
       (find-ith n pre-color)]
      [else ; spill
       (if (odd? n)
           (Deref 'rbp (- (* (ceiling  (/ (- n 10) 2)) 8)))
           (Deref 'r15 (* (/ (- n 10) 2) 8)))])))

; find-ith : Number [DictionaryOf Reg Number(Color)] -> Location
(define (find-ith n ls)
  (cond
    [(empty? ls) (Reg 'r15)] ; shouldn't happen
    [else (cond
            [(= n (cdar ls)) (caar ls)]
            [else (find-ith n (rest ls))])]))

; num-normal-spilled : [Listof Location] -> Number
(define (num-normal-spilled list)
  (length (filter (λ (loc)
                    (eq? 'rbp (Deref-reg loc)))
                  (filter Deref? list))))

; num-root-spilled : [Listof Location] -> Number
(define (num-root-spilled list)
  (length (filter (λ (loc)
                    (eq? 'r15 (Deref-reg loc)))
                  (filter Deref? list))))

; assign-homes-instrs : [ListOf Instr] [ListOf [PairOf Symbol (Deref reg int)]] -> [ListOf Instr]
(define (assign-homes-instrs instrs alist)
  (cond
    [(empty? instrs) empty]
    [else (cons (assign-homes-single (car instrs) alist)
                (assign-homes-instrs (cdr instrs) alist))]))

; assign-homes-single : Instr [ListOf [PairOf Var/Reg Reg/Deref]] -> Instr
(define (assign-homes-single instr alist)
  (match instr
    [(Instr op `,ls)
     (Instr op (map (λ (arg)
                      (match arg
                        [(Var var) (dict-ref alist (Var var))]
                        [else arg]))
                    ls))]
    [(TailJmp arg int)
     (define new-arg
       (match arg
         [(Var var) (dict-ref alist (Var var))]
         [else arg]))
     (TailJmp new-arg int)]
    [(IndirectCallq arg int)
     (define new-arg
       (match arg
         [(Var var) (dict-ref alist (Var var))]
         [else arg]))
     (IndirectCallq new-arg int)]
    [else instr])) 

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(ProgramDefs info ds)
     (define ds^
       (for/list ([d ds])
         (match d
           [(Def f inputs type info blocks)
            (define newblocks
              (map (λ (pr)
                     (begin
                       (define label (car pr))
                       (define block (cdr pr))
                       (define instrs-after-removing-duplicate
                         (match block
                           [(Block binfo instructions)
                            (foldr (λ (instr rest)
                                     (match instr
                                       [(Instr 'movq `(,arg1 ,arg2))
                                        (if (equal? arg1 arg2)
                                            rest ;; remove instrs in case of (movq (list -8(%rbp) -8(%rbp)))
                                            (append (patch-instructions-instr instr) rest))]
                                       [else (append (patch-instructions-instr instr) rest)]))                                      
                                   '()
                                   instructions)]))
                       (define instrs-handling-cmpq-movzbq
                         (foldr (λ (instr rest)
                                  (let ([new-instrs
                                         (match instr
                                           [(Instr 'cmpq `(,arg1 ,arg2))
                                            #:when (Imm? arg2)
                                            (list (Instr 'movq (list arg2 (Reg 'rax)))
                                                  (Instr 'cmpq (list arg1 (Reg 'rax))))]
                                           [(Instr 'movzbq `(,arg1 ,arg2))
                                            #:when (not (Reg? arg2))
                                            (list (Instr 'movzbq (list arg1 (Reg 'rax)))
                                                  (Instr 'movq (list (Reg 'rax) arg2)))]
                                           [_ (list instr)])])
                                    (append new-instrs rest)))
                                '() instrs-after-removing-duplicate))
                       (define leaq-and-tailjmp
                         ; dest of leaq must be a register
                         ; TailJmp takes rax
                         (foldr (λ (instr rest)
                                  (define instr^ ; [ListOf Instr]
                                    (match instr
                                      [(Instr 'leaq `(,arg1 ,arg2))
                                       (if (Reg? arg2)
                                           (list instr)
                                           (list (Instr 'leaq (list arg1 (Reg 'rax)))
                                                 (Instr 'movq (list (Reg 'rax) arg2))))]
                                      [(TailJmp arg int)
                                       (if (Reg? arg)
                                           (if (eq? (Reg-name arg) 'rax)
                                               (list instr)
                                               (list (Instr 'movq (list arg (Reg 'rax)))
                                                     (TailJmp (Reg 'rax) int)))
                                           (list (Instr 'movq (list arg (Reg 'rax)))
                                                 (TailJmp (Reg 'rax) int)))]
                                      [_ (list instr)]))
                                  (append instr^ rest)) '() instrs-handling-cmpq-movzbq))
                       (cons label (Block '() leaq-and-tailjmp))))
                   blocks))
            (Def f inputs type info newblocks)])))
     (ProgramDefs info ds^)]))

; patch-instructions-instr : Instr -> [ListOf Instr]
(define (patch-instructions-instr instr)
  (match instr
    [(Instr op `(,arg1 ,arg2))
     (cond
       [(both-memory? (list arg1 arg2)) (list (Instr 'movq (list arg1 (Reg 'rax)))
                                              (Instr op (list (Reg 'rax) arg2)))] 
       [else (list instr)])]
    [else (list instr)]))

; both-memory? : [ListOf Arg] -> Boolean
(define (both-memory? loa)
  (and (Deref? (car loa)) (Deref? (cadr loa))))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(ProgramDefs pinfo defs)
     (define labels-blocks
       (for/foldr ([acc '()])
                  ([def defs])
         (match def
           [(Def f '() type dinfo blocks)
            (define blocks^
              (for/list ([label-block blocks])
                (match-let ([(cons label block) label-block])
                  (define block^
                    (remove-tailjmp block dinfo))
                  (cons label block^))))
            
            (define main-conc-attached
              (append (list (build-prelude dinfo f))
                      blocks^
                      (list (build-conclusion dinfo f))))

            (append main-conc-attached acc)])))

     (X86Program pinfo labels-blocks)]))

; remove-tailjmp : Block Dictionary -> Block
(define (remove-tailjmp b info)
  (match b
    [(Block binfo instrs)
     (define instrs^
       (for/foldr ([acc '()])
                  ([instr instrs])
         (append (match instr
                   [(TailJmp (Reg 'rax) n)
                    (append (list (Instr 'subq (list (Imm (* 8 (dict-ref info 'num-root-spills)))
                                                     (Reg 'r15)))
                                  (Instr 'addq (list (compute-rsp info) (Reg 'rsp))))
                            (foldl (λ (s rest) (cons (Instr 'popq (list s)) rest))
                                   (list (Instr 'popq (list (Reg 'rbp)))
                                         (IndirectJmp (Reg 'rax)))
                                   (set->list (dict-ref info 'used-callee))))]
                   [else (list instr)])
                 acc)))
     (Block binfo instrs^)]))

; build-prelude : info Symbol -> (cons label Block)
(define (build-prelude info f)
  (let ([setup
         (append
          (list (Instr 'pushq (list (Reg 'rbp)))
                (Instr 'movq (list (Reg 'rsp) (Reg'rbp))))
          (foldr (λ (s rest) (cons (Instr 'pushq (list s)) rest))
                 '() (set->list (dict-ref info 'used-callee)))
          (list (Instr 'subq (list (compute-rsp info) (Reg 'rsp))))
          
          (if (eq? f 'main)
              (list (Instr 'movq (list (Imm 65536) (Reg 'rdi)))
                    (Instr 'movq (list (Imm 65536) (Reg 'rsi)))
                    (Callq 'initialize 2))
              '())
          
          (list (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15)))
                (Instr 'movq (list (Imm 0) (Deref 'r15 0)))
                (Instr 'addq (list (Imm (* 8 (dict-ref info 'num-root-spills))) (Reg 'r15))) ;; relating to rootstack
                (Jmp (symbol-append f 'start))))])
    
    (cons f (Block '() setup))))

; compute-rsp : info -> (Imm Number)
(define (compute-rsp info)
  (let* ([callees (length (dict-ref info 'used-callee))]
         [spills (dict-ref info 'num-spill)])
    (Imm (- (align (+ (* 8 callees) (* 8 spills)) 16) (* 8 callees)))))

; build-conclusion : info -> (cons label Block)
(define (build-conclusion info f)
  (let ([setup
         (append (list (Instr 'subq (list (Imm (* 8 (dict-ref info 'num-root-spills))) (Reg 'r15)))
                       (Instr 'addq (list (compute-rsp info) (Reg 'rsp))))
                 (foldl (λ (s rest) (cons (Instr 'popq (list s)) rest))
                        (list (Instr 'popq (list (Reg 'rbp)))
                              (Retq))
                        (set->list (dict-ref info 'used-callee))))])
    (cons (symbol-append f 'conclusion) (Block '() setup))))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(("shrink" ,shrink ,interp-Lfun ,type-check-Lfun)
    ("uniquify" ,uniquify ,interp-Lfun)
    ("reveal functions" ,reveal-functions ,interp-Lfun-prime)
    ("limit functions" ,limit-functions ,interp-Lfun-prime ,type-check-Lfun)
    ("expose allocation" ,expose-allocation ,interp-Lfun-prime)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime)
    ("explicate control" ,explicate-control ,interp-Cfun)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
    ("liveness analysis" ,uncover-live ,interp-pseudo-x86-3)
    ("build interference graph" ,build-interference ,interp-pseudo-x86-3)
    ("allocate registers" ,allocate-registers ,interp-x86-3)
    ("patch instructions" ,patch-instructions ,interp-x86-3)
    ("prelude-and-conclusion" ,prelude-and-conclusion #f)
    ))