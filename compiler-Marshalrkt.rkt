;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Group members: Marshal Gress, Weifeng Han, Nick Irmscher
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Ldyn.rkt")
(require "interp-Lany.rkt")
(require "interp-Lany-prime.rkt")
(require "type-check-Lany.rkt")
(require "interp-Cany.rkt")
(require "type-check-Cany.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require graph)
(require "graph-printing.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(require data/queue)
(provide (all-defined-out))

#|
LDyn concrete

cmp ::= eq? | < | <= | > | >=

exp ::= int | (read) | (- exp) | (+ exp exp) | (- exp exp)
        | var | (let ([var exp]) exp)
        | #t | #f | (and exp exp) | (or exp exp) | (not exp)
        | (cmp exp exp) | (if exp exp exp)
        | (vector exp...) | (vector-ref exp exp)
        | (vector-length exp)
        | (vector-set! exp exp exp) | (void)
        | (exp exp...) | (boolean? exp) | (integer? exp)
        | (vector? exp)  | (void? exp)

def ::= (define (var var ...) exp)

LDyn ::= def ... exp

----------------------------
LDyn Abstract

exp ::= (Int int) | (Var var) | (Let var exp exp)
        | (Prim op (exp...))
        | (Bool bool) | (If exp exp exp)
        | (Void) | (Apply exp exp...)

def ::= (Def var (var ...) ’Any ’() exp)

LDyn ::= (ProgramDefsExp ’() (def ...) exp)
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; shrink

; shrink : LDyn -> LDyn
(define (shrink p)
  (match p
    [(ProgramDefsExp info defs exp)
     (define new-defs
       (for/list ([def defs])
         (match def
           [(Def f params 'Any '() exp)
            (Def f params
                 'Any '()
                 (shrink-exp exp))])))
     (ProgramDefs info
                  (append new-defs
                          (list (Def 'main '()
                                     'Integer '()
                                     (shrink-exp exp)))))]
    
    [(Program info exp)
     (ProgramDefs info
                  (list (Def 'main '()
                             'Integer '()
                             (shrink-exp exp))))]))

; shrink-exp : exp -> exp
(define (shrink-exp e)
  (define recur shrink-exp)
  (match e
    [atm #:when (atom? atm)
         atm]
    [(Prim 'and `(,e1 ,e2)) (If (recur e1) (recur e2) (Bool #f))]
    [(Prim 'or  `(,e1 ,e2)) (If (recur e1) (Bool #t) (recur e2))]
    [(Prim op ls)
     (Prim op (map recur ls))]
    [(Let x e body)
     (Let x (recur e) (recur body))]
    [(If cnd thn els)
     (If (recur cnd) (recur thn) (recur els))]
    [(SetBang x e)
     (SetBang x (recur e))]
    [(Begin es end)
     (Begin (map recur es)
            (recur end))]
    [(WhileLoop cnd body)
     (WhileLoop (recur cnd)
                (recur body))]
    [(HasType e^ t)
     (HasType (recur e^) t)]
    [(Apply f params)
     (Apply (recur f)
            (map recur params))]
    [else (error "shrink-exp unmatched case" e)]))

; atom? : exp -> Boolean
(define (atom? e)
  (or (Int? e)
      (Var? e)
      (Bool? e)
      (Void? e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; uniquify

;; uniquify : LDyn U LAny' -> LDyn
(define (uniquify p)  
  (match p
    [(ProgramDefs info defs)
     (define funcs-env
       (for/list ([def defs])
         (define name
           (Def-name def))
         (cons name
               (if (eq? name 'main)
                   'main
                   (replace-hyphens (gensym name))))))
     (ProgramDefs
      info
      (for/list ([def defs])
        (match def
          [(Def f params rt '() exp)
           (define params-env
             (map (λ (x)
                    (match x
                      [y #:when (symbol? y)
                         (cons y (gensym y))]
                      [`[,y : ,type] ; after expose-allocation
                       (cons y (gensym y))]))
                  params))
           (define env^
             (append params-env
                     funcs-env))
           (define params^
             (map (λ (x)
                    (match x
                      [y #:when (symbol? y)
                         (dict-ref params-env y)]
                      [`[,y : ,type] ; after expose-allocation
                       `[,(dict-ref params-env y) : ,type]]))
                  params))
           (Def (dict-ref funcs-env f)
                params^
                rt '()
                ((uniquify-exp env^) exp))])))]))

; (uniquify-exp [env : alist]) : exp -> exp
(define (uniquify-exp env)
  (lambda (e)
    (define recur (uniquify-exp env))
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      
      [(Int n) e]
      [(Bool b) e]
      [(Void) e]
      
      [(Let x e body)
       (let* ([y (gensym x)]
              [new-env (dict-set env x y)])
         (Let y ((uniquify-exp new-env) e)
              ((uniquify-exp new-env) body))
         #;(if (member x (dict-values env))
             (Let x (recur e)
                  (recur body))
             (Let y ((uniquify-exp new-env) e)
                  ((uniquify-exp new-env) body))))]
      
      #;[(Prim 'vector-ref es)
       (Prim 'vector-ref (map recur es))]
      #;[(Prim 'vector-set! (list (Var v) n e^))
       (Prim 'vector-set! (list (Var (dict-ref env v))
                                n
                                (recur e^)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) (recur e)))]
      
      [(If test then else)
       (If (recur test)
           (recur then)
           (recur else))]
      
      [(SetBang x e)
       (SetBang (dict-ref env x) (recur e))]
      [(Begin es end)
       (Begin (map recur es)
              (recur end))]
      [(WhileLoop cnd body)
       (WhileLoop (recur cnd)
                  (recur body))]

      [(HasType e^ t)
       (HasType (recur e^) t)]
      [(GlobalValue x) e]
      [(Allocate n t) e]
      [(Collect n) e]

      [(Apply f params)
       (Apply (recur f)
              (map recur params))]
      [(FunRef f)
       (FunRef (dict-ref env f))]

      [(ValueOf e t)
       (ValueOf (recur e) t)]
      [(Exit) (Exit)])))

; replace-hyphens : Symbol -> Symbol
; for creating labels without hyphens in x86 code
(define (replace-hyphens s)
  (string->symbol
   (string-replace
    (symbol->string s)
    "-" "_")))

;(symbol-replace 'add-all)
;(symbol-replace 'addall)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; reveal functions

; reveal-functions : LDyn -> LDyn
(define (reveal-functions p)
  (match p
    [(ProgramDefs info defs)
     (define functions
       (for/list ([def defs])
         (Def-name def)))
     (ProgramDefs
      info
      (for/list ([def defs])
        (match def
          [(Def f params rt '() e)
           (Def f params rt '() ((rf-exp functions) e))])))]))

; rf-exp : exp [Listof Symbol] -> exp
; reveal functions in an expression
(define (rf-exp functions)
  (λ (e)
    (define recur (rf-exp functions))
    (match e
      [(Var x)
       (if (member x functions)
           (FunRef x)
           (Var x))]
    
      [atm #:when (atom? atm) atm]
      [(Prim op es)
       (Prim op (map recur es))]
      [(Let x rhs body)
       (Let x (recur rhs)
            (recur body))]
    
      [(If cnd then else)
       (If (recur cnd)
           (recur then)
           (recur else))]
    
      [(SetBang x e^)
       (SetBang x (recur e^))]
      [(Begin es end)
       (Begin (map recur es)
              (recur end))]
      [(WhileLoop cnd body)
       (WhileLoop (recur cnd)
                  (recur body))]

      [(HasType e^ t)
       (HasType (recur e^) t)]
    
      [(Apply f es)
       (Apply (recur f) (map recur es))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; cast insertion

#| LAny
type ::= Any

op ::= any-vector-length | any-vector-ref | any-vector-set!
       | boolean? | integer? | vector? | procedure? | void?

exp ::= (Inject exp ftype) | (Project exp ftype)

def ::= (Def name ([x : Any] ...) 'Any info exp)

LAny ::= (ProgramDefsExp ’() (def ...) exp)

(define (any-tag ty)
  (match ty
    ['Integer 1]		;; 001
    [`(Vector ,ts ...) 2]	;; 010
    [`(PVector ,ts ...) 2]
    [`(,ts ... -> ,rt) 3]	;; 011
    ['Boolean 4]		;; 100
    ['Void 5]                   ;; 101
    [`(Vectorof ,t) 6]          ;; 110
    [else (error "in any-tag, unrecognized type" ty)]
    ))

|#

; insert-casts : LDyn -> LAny
(define (insert-casts p)
  (match p
    [(ProgramDefs info defs)
     (define alist
       (for/list ([def defs])
         (match def
           [(Def f params rt '() exp)
            (cons f (length params))])))
     (define defs^
       (for/list ([def defs])
         (match def
           [(Def f params rt '() exp)
            (define exp^
              ((insert-casts-exp alist) exp))
            (define params^
              (for/list ([p params])
                `[,p : Any]))
            (Def f params^
                 rt '()
                 (if (eq? f 'main)
                     (Project exp^ 'Integer)
                     exp^))])))
     (ProgramDefs info defs^)]))

; insert-casts-exp : LDyn_exp Dictionary -> LAny_exp
; num-params is the arity of the function, used for FunRefArity
(define (insert-casts-exp arities)
  (λ (exp)
    (define recur (insert-casts-exp arities))
    (match exp
      [(Var x) exp]
      [(Int n) (Inject exp 'Integer)]
      [(Bool b) (Inject exp 'Boolean)]
      ;[(Void) (Inject exp 'Void)]

      [(Let x e body)
         (let ([e^ (recur e)]
               [body^ (recur body)])
           (Let x e^ body^))]

      [(Prim 'eq? `(,e1 ,e2))
       (let ([e1^ (recur e1)]
             [e2^ (recur e2)])
         (Inject (Prim 'eq? (list e1^ e2^))
                 'Boolean))]
      [(Prim 'not `(,e))
       (let ([e^ (recur e)])
         (If (Prim 'eq? (list e^ (Inject (Bool #f) 'Boolean)))
             (Inject (Bool #t) 'Boolean)
             (Inject (Bool #f) 'Boolean)))]
      [(Prim op es)
       #:when (or (eq? '- op)
                  (eq? '+ op))
       (insert-casts-prim exp 'Integer 'Integer recur)]
      [(Prim op es)
       #:when (or (eq? 'and op)
                  (eq? 'or op))
       (insert-casts-prim exp 'Boolean 'Boolean recur)]
      [(Prim op es)
       #:when (cmp? op)
       (insert-casts-prim exp 'Integer 'Boolean recur)]
      [(Prim op es)
       #:when (pred? op)
       (let ([es^ (map recur es)])
         (Inject (Prim op es^) 'Boolean))]
      [(Prim 'read '())
       (Inject exp 'Integer)]

      [(If cnd then else)
       (let ([cnd^ (recur cnd)]
             [then^ (recur then)]
             [else^ (recur else)])
         (If (Prim 'eq? (list cnd^ (Inject (Bool #f) 'Boolean)))
             else^
             then^))]

      #|[(WhileLoop cnd body)
     (let ([cnd^ (recur cnd)]
           [body^ (recur body)])
       (Inject (WhileLoop cnd^ body^) 'Void))]
    [(SetBang x e)
     (let ([e^ (recur e)])
       (Inject (SetBang x e^) 'Void))]
    [(Begin es end)
     (let ([end^ (recur end)]
           [es^ (map recur es)])
       (match end^
         [(Tagged e tag)
          (Inject (Begin es^ end^) tag)]))] ; ?|#

      [(Prim 'vector es)
       (let ([es^ (map recur es)])
         (Inject (Prim 'vector es^)
                 (append '(Vector)
                          (build-list (length es^)
                                      (λ (n) 'Any)))))]
      [(Prim 'vector-ref `(,e1 ,e2))
       (let ([e1^ (recur e1)]
             [e2^ (Project (recur e2) 'Integer)])
         (Prim 'any-vector-ref (list e1^ e2^)))]
      [(Prim 'vector-set! `(,e1 ,e2 ,e3))
       (let ([e1^ (recur e1)]
             [e2^ (Project (recur e2) 'Integer)]
             [e3^ (recur e3)])
         (Prim 'any-vector-set! (list e1^ e2^ e3^)))]
      [(Prim 'vector-length `(,v))
       (let ([v^ (recur v)])
         (Inject (Prim 'any-vector-length (list v^)) 'Integer))]

      [(Apply f ps)
       (let* ([ps^ (map recur ps)]
              [f^ (recur f)]
              [ftype (append (build-list (length ps^)
                                         (λ (n) 'Any))
                             '(-> Any))])
         (Apply (Project f^ ftype) ps^))]
      [(FunRef f)
       (define arity (dict-ref arities f))
       (Inject (FunRef f)
               (append (build-list arity
                                   (λ (n) 'Any))
                       '(-> Any)))])))
    

; insert-casts-prim : LDyn_exp Symbol Symbol Function -> LAny_exp
(define (insert-casts-prim exp pt rt recur)
  (match exp
    [(Prim op es)
     (Inject (Prim op (for/list ([e es])
                        (Project (recur e)
                                 pt)))
             rt)]
    [else (error "inject-casts-prim expected Prim exp, got" exp)]))

; pred? : Symbol -> Boolean
(define (pred? name)
  (or (eq? name 'boolean?)
      (eq? name 'integer?)
      (eq? name 'vector?)
      (eq? name 'procedure?)
      (eq? name 'void?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; reveal casts

; reveal-casts : LAny -> LAny'
(define (reveal-casts p)
  (match p
    [(ProgramDefs info defs)
     (define defs^
       (for/list ([def defs])
         (match def
           [(Def f params rt '() body)
            (Def f params rt '() (reveal-casts-exp body))])))
     (ProgramDefs info defs^)]))

; reveal-casts-exp : exp -> exp
(define (reveal-casts-exp exp)
  (define recur reveal-casts-exp)
  (match exp
    [e #:when (atom? e) e]
    [(Inject e fT)
     (let ([e^ (recur e)])
       (Prim 'make-any (list e^ (Int (any-tag fT)))))]
    [(Project e fT)
     (match fT
       [(or 'Boolean 'Integer)
        (let ([e^ (recur e)]
              [tmp (gensym 'tmp)])
          (Let tmp e^
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                    (Int (any-tag fT))))
                   (ValueOf (Var tmp) fT)
                   (Exit))))]
       ['(Vector Any ...)
        (let ([e^ (recur e)]
              [tmp (gensym 'tmp)])
          (Let tmp e^
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                    (Int (any-tag fT))))
                   (If (Prim 'eq? (list (Prim 'vector-length (list (Var tmp)))
                                        (Int (sub1 (length fT)))))
                       (ValueOf (Var tmp) fT)
                       (Exit))
                   (Exit))))]
       [`(,ts ... -> ,rt)
        (let ([e^ (recur e)]
              [tmp (gensym 'tmp)])
          (Let tmp e^
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                    (Int (any-tag fT))))
                       (ValueOf (Var tmp) fT)
                       (Exit))))])]
    [(Let x e body)
     (Let x (recur e) (recur body))]
    [(If cnd then else)
     (If (recur cnd)
         (recur then)
         (recur else))]
    [(Prim op `(,e))
     #:when (pred? op)
     (let ([e^ (recur e)]
           [tmp (gensym 'tmp)]
           [type (pred->tag op)])
       (Let tmp e^
            (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp)))
                                 (Int (any-tag type))))
                (Bool #t)
                (Bool #f))))]
    [(Prim 'any-vector-ref `(,e1 ,e2))
     (let ([e1^ (recur e1)]
           [e2^ (recur e2)]
           [v (gensym 'v)]
           [i (gensym 'i)])
       (Let v e1^
            (Let i e2^
                 (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var v))) (Int 2)))
                     (If (Prim '< (list (Var i)
                                        (Prim 'any-vector-length (list (Var v)))))
                         (Prim 'any-vector-ref (list (Var v) (Var i)))
                         (Exit))
                     (Exit)))))]
    [(Prim 'any-vector-set! `(,e1 ,e2 ,e3))
     (let ([e1^ (recur e1)]
           [e2^ (recur e2)]
           [e3^ (recur e3)]
           [v (gensym 'v)]
           [i (gensym 'i)]
           [e (gensym 'e)])
       (Let v e1^
            (Let i e2^
                 (Let e e3^
                      (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var v))) (Int 2)))
                          (If (Prim '< (list (Var i)
                                             (Prim 'any-vector-length (list (Var v)))))
                              (Prim 'any-vector-set! (list (Var v) (Var i) (Var e)))
                              (Exit))
                          (Exit))))))]
    [(Prim op es)
     (Prim op (map recur es))]
    [(Apply f ps)
     (Apply (recur f)
            (map recur ps))]
    [(FunRef f)
     (FunRef f)]))

; pred->tag : Symbol -> Symbol
(define (pred->tag p)
  (match p
    ['integer? 'Integer]
    ['vector? '(Vector Any)]
    ['procedure? '(Any -> Any)]
    ['boolean? 'Boolean]
    ['void? 'Void]))
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; limit functions

; limit-functions : LAny' -> LAny'
(define (limit-functions p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs
      info
      (for/list ([def defs])
        (match def
          [(Def f params rt '() body)
           (define params^ (limit-params params 1))
           (define tup
             (if (= (length params^) 6)
                 (sixth params^)
                 (list 'tup ': '(Vector))))
           (define body^ ((transform-body tup params) body))
           (Def f params^ rt '() body^)])))]))
               

; limit-params : [Listof [Symbol : Type]] Integer -> [Listof [Symbol : Type]]
(define (limit-params ps i)
  (cond
    [(> i 5)
     (if (<= (length ps) 1) ; reached last arg (vector not needed)
         ps
         `([,(gensym 'tup)
            : ,(cons 'Vector
                     (map (λ (var-type)
                            (match var-type
                              [`[,var : ,type]
                               type]))
                          ps))]))]
    [else
     (if (empty? ps)
         '()
         (cons (car ps)
               (limit-params (cdr ps) (add1 i))))]))

; transform-body : [List Symbol ': VectorType] [Listof [Symbol : Type]]
;                  [Listof [Symbol : Type]] -> exp -> exp
(define (transform-body tup params)
  (λ (e)
    (define recur (transform-body tup params))
    (match tup
      [`[,name : ,type]
       (match e
         [(Var x)
          (define member (assoc x params))
          (if member
              (let ([i (index-of params member)])
                (if (< i 5)
                    e
                    (match type
                      [`(Vector ,rest ...)
                       (Prim 'vector-ref
                             (list (Var name)
                                   (Int (- i 5))))]
                      [else e])))
              e)]
         [atm #:when (atom? atm)
              atm]

         [(Prim op es)
          (Prim op
                (for/list ([e^ es])
                  (recur e^ )))]
         [(Let x rhs body)
          (Let x (recur rhs)
               (recur body))]
    
         [(If cnd then else)
          (If (recur cnd)
              (recur then)
              (recur else))]
    
         [(SetBang x e^) ; !
          (SetBang x (recur e^))]
         [(Begin es end)
          (Begin (for/list ([e^ es])
                   (recur e^))
                 (recur end))]
         [(WhileLoop cnd body)
          (WhileLoop (recur cnd)
                     (recur body))]

         [(HasType e^ t)
          (HasType (recur e^) t)]
    
         [(Apply f es)
          (if (> (length es) 6)
              (let ([rest (list-tail es 5)])
                (Apply (recur f)
                       (list (recur (first es))
                             (recur (second es))
                             (recur (third es))
                             (recur (fourth es))
                             (recur (fifth es))
                             (Prim 'vector
                                   (for/list ([e^ rest])
                                     (recur e^))))))
          ; else
              (Apply (recur f)
                     (for/list ([e^ es])
                       (recur e^))))]
         [(FunRef f) (FunRef f)]

         [(ValueOf e t)
          (match t
            [(or '(-> Any)
                 `(Any ... -> Any))
              (ValueOf (recur e) (limit-types t 0))]
            [else (ValueOf (recur e) t)])]
         [(Exit) (Exit)])])))

; limit-types : [Listof Symbol] -> [Listof Symbol]
(define (limit-types types i)
  (cond
    [(eq? (car types) '->) types]
    [(eq? i 5)
     (match types
       ['(-> Any) types]
       ['(Any -> Any) types]
       [else 
        (define v
          (for/fold ([acc '(Vector)])
                    ([type types])
            #:break (eq? type '->)
            (append acc `(,type))))
        (cons v '(-> Any))])]
    [else (cons (car types)
                (limit-types (cdr types) (add1 i)))]))

;(limit-types '(-> Any) 0)
;(limit-types '(Any -> Any) 0)
;(limit-types '(Any Any -> Any) 0)
;(limit-types '(Any Any Any -> Any) 0)
;(limit-types '(Any Any Any Any -> Any) 0)
;(limit-types '(Any Any Any Any Any -> Any) 0)
;(limit-types '(Any Any Any Any Any Any -> Any) 0)
;(limit-types '(Any Any Any Any Any Any Any -> Any) 0)
;(limit-types '(Any Any Any Any Any Any Any Any -> Any) 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; expose allocation

#| RAlloc
exp ::= ... | (Prim vector-ref (exp (Int int)) 
      | (Prim vector-set! (exp (Int int) exp))
      | (Collect int) | (Allocate int type) | (GlobalValue name)

RAlloc ::= (Program ’() exp)

- The (collect n) form runs the garbage collector, requesting that it make sure
that there are n bytes ready to be allocated.
- The (allocate n T) form obtains memory for n elements (and space at the front for the
64 bit tag), but the elements are not initialized.
|#

; expose-allocation : LAny' -> LAny'
(define (expose-allocation p)
  (match p
    [(ProgramDefs info defs)
     (uniquify ; uniquify newly created variables
      (ProgramDefs
       info
       (for/list ([def defs])
         (match def
           [(Def name params type '() body)
            (Def name params type '() (expose-alloc-exp body))]))))]))

; expose-alloc-exp : Rvec-exp -> Ralloc-exp
(define (expose-alloc-exp e)
  (define recur expose-alloc-exp)
  (match e
    [(HasType v t)
     (match v
       [(Prim 'vector es)
        (let* ([len (length es)]
               [bytes (+ 8 (* 8 len))]
               [sets (gen-sets 0 len)]
               [rest (Let '_ (gen-collect bytes)
                          (Let 'v (Allocate len t)
                               sets))])
          (tmps-es v rest 0))])]

    [e #:when (atom? e)
       e]
    [(Let x rhs body)
     (Let x
          (recur rhs)
          (recur body))]
    [(Prim op es)
     (Prim op (map recur es))]
    [(If cnd then else)
     (If (recur cnd)
         (recur then)
         (recur else))]
    [(SetBang var exp)
     (SetBang var (recur exp))]
    [(Begin es end)
     (Begin (map recur es)
            (recur end))]
    [(WhileLoop cnd body)
     (WhileLoop (recur cnd)
                (recur body))]

    [e #:when (or (Collect? e)
                  (Allocate? e)
                  (GlobalValue? e))
       e] ; recursive calls in tmps-es create Ralloc exps

    [(Apply f params)
     (Apply (recur f)
            (map recur params))]
    [(FunRef f) (FunRef f)]

    [(ValueOf e t)
     (ValueOf (recur e) t)]
    [(Exit) (Exit)]))

; tmps-es : Vector exp Int -> Let-exp
(define (tmps-es v base i)
  (match v
    [(Prim 'vector es)
     (define es^ (map expose-alloc-exp es))
     (cond
       [(empty? es^) base]
       [else (let ([name (string->symbol (string-append "e" (number->string i)))]
                   [e^ (car es^)]
                   [cont (Prim 'vector (cdr es^))])
               (Let name e^ (tmps-es cont base (add1 i))))])]

    [else (error "tmps-es: expected a vector, got" v)]))

;(tmps-es (Prim 'vector (list (Int 15) (Int 9) (Bool #t))) (Int 42) 0)

; gen-collect : Integer -> If-exp
(define (gen-collect bytes)
  (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr)
                                    (Int bytes)))
                     (GlobalValue 'fromspace_end)))
      (Void)
      (Collect (Int bytes))))

;(gen-collect 64)

; gen-sets : Integer Integer -> Let-exp
(define (gen-sets i len)
  (cond
    [(= i len) (Var 'v)]
    [else (let ([name (string->symbol (string-append "e" (number->string i)))]
                [cont (gen-sets (add1 i) len)])
            (Let (string->symbol (string-append "_" (number->string i)))
                 (Prim 'vector-set!
                       (list (Var 'v)
                             (Int i)
                             (Var name)))
                 cont))]))

;(gen-sets 0 10)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; remove complex operands

; pass-defs : [Listof Def] Function -> Def
(define (pass-defs defs exp-pass)
  (for/list ([def defs])
    (match def
      [(Def name params type '() body)
       (Def name params type '() (exp-pass body))])))
    
; remove-complex-opera* : LFunRef -> LFunRef_ANF
(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info (pass-defs defs rco-exp))]))

; rco-exp : Exp -> Exp
(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Let x e body)
     (Let x (rco-exp e) (rco-exp body))]
    [(If cnd thn els)
     (If (rco-exp cnd) (rco-exp thn) (rco-exp els))]
    [(Prim op es)
     (define lod (map rco-atom es))
     (define newes (map car lod))
     (define dict (foldr (λ (pr l)
                           (append (cdr pr) l))
                         '()
                         lod))
     (update (Prim op newes) dict)]
    
    [(SetBang x e)
     (SetBang x (rco-exp e))]
    [(Begin es end)
     (Begin (map rco-exp es)
            (rco-exp end))]
    [(WhileLoop cnd body)
     (WhileLoop (rco-exp cnd)
                (rco-exp body))]
    
    [(Collect n) e]
    [(Allocate n t) e]
    [(GlobalValue x) e]
    
    [(Apply f params)
     (define rco-f (rco-atom f))
     (define rco-pairs (map rco-atom params))
     (define rco-params (map car rco-pairs))
     (define dict
       (append (cdr rco-f)
               (foldr (λ (pr l)
                        (append (cdr pr) l))
                      '()
                      rco-pairs)))
     (update (Apply (car rco-f) rco-params) dict)]
    [(FunRef f) e]

    [(ValueOf exp t)
     (define pair (rco-atom exp))
     (define exp^ (car pair))
     (define dict (cdr pair))
     (update (ValueOf exp^ t) dict)]
    [(Exit) e]))

; rco-atom : Exp -> (list Atom [DictionaryOf Symbol Exp])
(define (rco-atom e)
  (match e
    [(Var x)
     (define atm (Var x))
     (define alist '())
     (cons atm alist)]
    [(Int n)
     (define atm (Int n))
     (define alist '())
     (cons atm alist)]
    [(Bool b)
     (define atm (Bool b))
     (define alist '())
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
     (define atm (if (atom? newbody)
                     newbody
                     (Var key)))
     (define alist (if (atom? newbody)
                       (dict-set '() x newe)
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
     (cons atm alist)]
    
    [(SetBang x e)
     (define tmp (gensym 'tmp))
     (define val (SetBang x (rco-exp e)))
     (define alist (dict-set '() tmp val))
     (cons (Var tmp) alist)]
    [(Begin es end)
     (define tmp (gensym 'tmp))
     (define val
       (Begin (map rco-exp es)
              (rco-exp end)))
     (define alist (dict-set '() tmp val))
     (cons (Var tmp) alist)]
    [(WhileLoop cnd body)
     (define tmp (gensym 'tmp))
     (define val
       (WhileLoop (rco-exp cnd)
                  (rco-exp body)))
     (define alist (dict-set '() tmp val))
     (cons (Var tmp) alist)]
    
    [(Collect n)
     (define tmp (gensym 'tmp))
     (define alist (dict-set '() tmp e))
     (cons (Var tmp) alist)]
    [(Allocate n t)
     (define tmp (gensym 'tmp))
     (define alist (dict-set '() tmp e))
     (cons (Var tmp) alist)]
    [(GlobalValue t)
     (define tmp (gensym 'tmp))
     (define alist (dict-set '() tmp e))
     (cons (Var tmp) alist)]

    [(Apply f params)
     (define fun (gensym 'fun))
     (define rco-f (rco-atom f))
     (define rco-pairs (map rco-atom params))
     (define rco-params (map car rco-pairs))
     (define dict
       (append (cdr rco-f)
               (foldr (λ (pr l)
                        (append (cdr pr) l))
                      '()
                      rco-pairs)))
     (define value (Apply (car rco-f) rco-params))
     (define alist (dict-set dict fun value))
     (cons (Var fun) alist)]
    [(FunRef f)
     (define tmp (gensym 'tmp))
     (define alist (dict-set '() tmp e))
     (cons (Var tmp) alist)]

    [(ValueOf exp t)
     (define tmp (gensym 'tmp))
     (define pair (rco-atom exp))
     (define exp^ (car pair))
     (define dict (cdr pair))
     (define dict^ (dict-set dict tmp e))
     (cons (Var tmp) dict^)]
    [(Exit)
     (define tmp (gensym 'tmp))
     (define alist (dict-set '() tmp e))
     (cons (Var tmp) alist)]))

; update : exp Dicitonary -> (Let var exp exp)
(define (update e dict)
  (cond
    [(dict-empty? dict) e]
    [else (let* ([x (car (car dict))]
                 [v (cdr (car dict))]
                 [body (update e (cdr dict))])
            (Let x v body))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; explicate control

#| CFun
atm ::= (Int int) | (Var var) | (Bool bool) | (Void)

cmp ::= eq? | < | <= | > | >=

exp ::= atm
      | (Void)
      | (Prim read ())
      | (Prim - (atm))
      | (Prim + (atm atm))
      | (Prim not (atm))
      | (Prim cmp (atm atm))
      | (Prim ’vector-ref (atm (Int int)))
      | (Prim ’vector-set! (atm (Int int) atm))
      | (GlobalValue var)
      | (Allocate int type)
      | (FunRef label) | Call(atm, (atm...))
      | (Prim ’any-vector-ref (atm atm))
      | (Prim ’any-vector-set! (list atm atm atm))
      | (ValueOf exp ftype)

stmt ::= (Assign (Var var) exp)
       | (Prim read ())
       | (Prim vector-set! (atm (Int int) atm))
       | (Collect int)

tail ::= (Return exp)
       | (Seq stmt tail)
       | (Goto label)
       | (IfStmt (Prim cmp (atm atm)) (Goto label) (Goto label))
       | (TailCall atm atm...)
       | (Exit)

def ::= (Def label ([var:type]...) type info ((label . tail)...))

CAny ::= (ProgramDefs info (def ...))
|#

;; explicate-control : RAlloc -> CTup
(define (explicate-control p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs
      info
      (for/list ([def defs])
        (explicate-def def)))]))

(define blocks (make-hash)) ; [Dictionaryof label tail]

; explicate-def : L-def -> C-def
(define (explicate-def def)
  (match def
    [(Def f params rt info body)
     (hash-clear! blocks)
     (let ([body-tail (explicate-tail body)])
       (dict-set! blocks
                  (symbol-append f 'start)
                  body-tail)
       (Def f params rt info (hash->list blocks)))]))

; explicate-tail : RIf_exp -> Cif_tail
; generates code for expressions in tail position
(define (explicate-tail e)
  (match e
    [(Var x) (Return e)]
    [(Int n) (Return e)]
    [(Bool b) (Return e)]
    [(Void) (Return e)]
    [(Prim op es) (Return e)]

    [(Let x rhs body)
     (let* ([bodyctail (explicate-tail body)])
       (explicate-assign rhs x bodyctail))]

    [(If test then else)
     (let* ([cthen (explicate-tail then)]
            [celse (explicate-tail else)])
       (explicate-pred test cthen celse))]

    [(SetBang x e)
     (explicate-assign e x (Return (Void)))]

    [(Begin es end)
     (foldl (λ (e cont)
              (explicate-effect e cont))
            (explicate-tail end)
            es)]

    [(WhileLoop cnd body)
     (explicate-effect body (Return (Void)))]

    [(Collect n)
     (Seq (Collect n) (Return (Void)))]
    [(Allocate n t)
     (Return e)]
    [(GlobalValue x)
     (Return e)]

    [(Apply f params)
     (TailCall f params)]
    [(FunRef f)
     (Return e)]

    [(ValueOf exp t)
     (Return e)]
    [(Exit) (Exit)]

    [else (error "explicate-tail unhandled case" e)]))

; explicate-assign : RIf_exp var CIf_tail -> Cif_tail
; generates code for a `let` by cases on the right-hand side expression
(define (explicate-assign e x cont)
  (match e
    [(Var s) (Seq (Assign (Var x) e) cont)]
    [(Int n)
     (Seq (Assign (Var x) e) cont)]
    [(Bool b) (Seq (Assign (Var x) e) cont)]
    [(Void) (Seq (Assign (Var x) e) cont)]
    [(Prim op es) (Seq (Assign (Var x) e) cont)]

    [(Let s rhs body)
     (let* ([bodyctail (explicate-assign body x cont)])
       (explicate-assign rhs s bodyctail))]

    [(If test then else)
     (let* ([cont-goto (create-block cont (gensym 'block))]
            [then-tail (explicate-assign then x cont-goto)]
            [else-tail (explicate-assign else x cont-goto)])
       (explicate-pred test then-tail else-tail))]

    [(SetBang x e)
     (Seq (Assign (Var x) e) cont)]

    [(Begin es end)
     (foldl (λ (e cont^)
              (explicate-effect e cont^))
            (explicate-assign end x cont)
            es)]

    [(WhileLoop cnd body)
     (let ([body-tail (explicate-assign body x cont)])
       (explicate-pred cnd body-tail (Return (Void))))]

    [(Collect n) (Seq e cont)]
    [(Allocate n t) (Seq (Assign (Var x) e) cont)]
    [(GlobalValue y) (Seq (Assign (Var x) e) cont)]

    [(Apply f params)
     (Seq (Assign (Var x) (Call f params)) cont)]
    [(FunRef f)
     (Seq (Assign (Var x) e) cont)]

    [(ValueOf exp t)
     (Seq (Assign (Var x) e) cont)]
    [(Exit)
     (Seq (Assign (Var x) e) cont)]

    [else (error "explicate-assign unhandled case" e)]))

; explicate-pred : RIf_exp CIf_tail CIf_tail -> CIf_tail
; generates code for an `if` expression by cases on the condition.
(define (explicate-pred cnd thn els)
  (match cnd
    [(Var x)
     (let ([thn-goto (create-block thn (gensym 'block))]
           [els-goto (create-block els (gensym 'block))])
       (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) ; x is a bool, (and x #t) works
               thn-goto
               els-goto))]

    [(Bool b) (if b thn els)]

    [(Prim 'not (list e))
     (explicate-pred e els thn)] ; switched thn and els

    [(Prim op es)
     #:when (or (cmp? op)
                (eq? 'vector-ref op))
     (let ([thn-goto (create-block thn (gensym 'block))]
           [els-goto (create-block els (gensym 'block))])
       (IfStmt cnd
               thn-goto
               els-goto))]

    [(Let x rhs body)
     (let ([body-tail (explicate-pred body thn els)])
       (explicate-assign rhs x body-tail))]

    [(If cnd^ thn^ els^)
     (let* ([thn-goto (create-block thn (gensym 'block))]
            [els-goto (create-block els (gensym 'block))]
            [thn^-tail (explicate-pred thn^ thn-goto els-goto)]
            [els^-tail (explicate-pred els^ thn-goto els-goto)])
       (explicate-pred cnd^ thn^-tail els^-tail))]

    [(Begin es end)
     (foldl (λ (e cont)
              (explicate-effect e cont))
            (explicate-pred end thn els)
            es)]

    [(GlobalValue x)
     (let ([thn-goto (create-block thn (gensym 'block))]
           [els-goto (create-block els (gensym 'block))])
       (IfStmt cnd
               thn-goto
               els-goto))]

    [(Apply f params)
     (let ([new-tmp (gensym 'tmp)]
           [thn-goto (create-block thn (gensym 'block))]
           [els-goto (create-block els (gensym 'block))])
       (explicate-assign cnd new-tmp
                         (IfStmt (Prim 'eq? (list (Var new-tmp) (Bool #t)))
                                 thn-goto
                                 els-goto)))]

    [else (error "explicate-pred unhandled case" cnd)]))

; explicate-effect : exp tail -> tail
(define (explicate-effect e tail)
  (match e
    [(Var x) tail]
    [(Int n) tail]
    [(Bool b) tail]

    [(Prim op es)
     (if (or (eq? op 'read)
             (eq? op 'vector-set!))
         (Seq e tail)
         tail)]

    [(Let x rhs body)
     (explicate-assign rhs x (explicate-effect body tail))]

    [(If test then else)
     (let* ([cthen (explicate-effect then tail)]
            [celse (explicate-effect else tail)])
       (explicate-pred test cthen celse))]

    [(SetBang x e)
     (explicate-assign e x tail)]

    [(Begin es end)
     (foldl (λ (e cont)
              (explicate-effect e cont))
            (explicate-effect end tail)
            es)]

    [(WhileLoop cnd body)
     (let* ([label (gensym 'loop)]
            [body^ (explicate-effect body (Goto label))]
            [loop-body (explicate-pred cnd body^ tail)])
       (create-block loop-body label))]

    [(Collect n)
     (Seq e tail)]
    [(Allocate n t)
     (Seq e tail)]

    [else (error "explicate-effect unhandled case" e)]))

; create-block : Cif_tail Symbol -> (Goto label)
(define (create-block tail label)
  (dict-set! blocks label tail)
  (Goto label))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; select instructions

#|  x86Global
bytereg ::= ah | al | bh | bl | ch | cl | dh | dl

arg ::= (Imm int) | (Reg reg) | (Deref reg int) | (ByteReg bytereg)
        | (Global var) | (FunRef label)

cc ::= e | l | le | g | ge

instr ::= (Instr addq (arg arg)) | (Instr subq (arg arg))
        | (Instr movq (arg arg)) | (Instr negq (arg))
        | (Callq label int) | (Retq) | (Instr popq (arg))
        | (Instr pushq (arg)) | (Jmp label)
        | (Instr xorq (arg arg)) | (Instr cmpq (arg arg))
        | (Instr set (cc arg)) | (Instr movzbq (arg arg))
        | (JmpIf cc label) | (IndirectCallq arg int)
        | (TailJmp arg int) | (Instr leaq (arg (Reg reg)))

block ::= (Block info (instr ...))

def ::= (Def label ’() type info ((label . block)...))

x86Global ::= (ProgramDefs info (def ...))
|#

; compute-tag : [Listof Any] -> Integer
(define (compute-tag types)
  (define pointer-mask
    (reverse
     (map (λ (t)
            (match t
              [(cons 'Vector types) 1]
              [else 0]))
          types)))
  (+ (arithmetic-shift (bin->dec pointer-mask) 7)
     (arithmetic-shift (length types) 1)))

; bin->dec : [Listof Integer] -> Integer
(define (bin->dec digits)
  (cond
    [(empty? digits) 0]
    [else (+ (* (car digits)
                (expt 2 (length (cdr digits))))
             (bin->dec (cdr digits)))]))

;(bin->dec (list 1 1 0 1 1 1))

; set-suffix : cmp -> cc
(define (set-suffix cmp)
  (match cmp
    ['eq? 'e]
    ['< 'l]
    ['<= 'le]
    ['> 'g]
    ['>= 'ge]))

; cmp? : Symbol -> Boolean
(define (cmp? op)
  (or (eq? op 'eq?) (eq? op '<) (eq? op '<=)
      (eq? op '>) (eq? op '>=)))

; si-tail : tail -> x86Global
(define si-tail
  (λ (func-name tail)
    (match tail
      [(Return exp)
       (append (si-exp exp (Reg 'rax))
               (list (Jmp (symbol-append func-name 'conclusion))))]
      [(Seq stmt tail)
       (append (si-stmt stmt)
               (si-tail func-name tail))]
      [(Goto label)
       (list (Jmp label))]
      
      [(IfStmt cnd (Goto l1) (Goto l2))
       (match cnd
         [(Prim op `(,atm1 ,atm2))
          #:when (cmp? op)
          (let ([cc (set-suffix op)]
                [arg1 (si-atm atm1)]
                [arg2 (si-atm atm2)])
            (list (Instr 'cmpq (list arg2 arg1))
                  (JmpIf cc l1)
                  (Jmp l2)))]
         [(Prim 'vector-ref `(,tup ,n))
          (list (Instr 'movq (list tup (Reg 'r11)))
                (Instr 'cmpq (list (Deref 'r11 (* 8 (add1 (Int-value n)))) (Imm 1)))
                (JmpIf 'e l1)
                (Jmp l2))])]

      [(TailCall f params)
       (append (si-call-params params 0)
               (list (TailJmp f (length params))))]
       
      [else (error "expected a tail for si-tail, instead got" tail)])))

; si-atm : atm -> X86-arg
(define si-atm
  (λ (atm)
    (match atm
      [(Int n) (Imm n)]
      [(Var x) (Var x)]
      [(Bool b)
       (match b
         [#t (Imm 1)]
         [#f (Imm 0)])]
      [(Void) (Imm 0)]
      [else (error "expected an atom for si-atm, instead got" atm)])))

; si-stmt : stmt -> x86Global
(define si-stmt
  (λ (stmt)
    (match stmt
      [(Assign (Var x) exp)
       (match exp
         ; special cases to prevent needless code
         [(Prim '+ `(,atm1 ,atm2))
          (cond
            [(equal? (Var x) atm1)
             (list (Instr 'addq (list (si-atm atm2) (Var x))))]
            [(equal? (Var x) atm2)
             (list (Instr 'addq (list (si-atm atm1) (Var x))))]
            [else (si-exp exp (Var x))])]

         [(Prim '- `(,atm1 ,atm2))
          (cond
            [(equal? (Var x) atm1)
             (list (Instr 'subq (list (si-atm atm2) (Var x))))]
            [else (si-exp exp (Var x))])]

         [(Prim 'not `(,atm1))
          (cond
            [(equal? (Var x) atm1)
             (list (Instr 'xorq (list (Imm 1) (Var x))))]
            [else
             (si-exp exp (Var x))])]
         ; ------------------------------------

         [else (si-exp exp (Var x))])]
      
      [(Prim op es)
       #:when (or (eq? op 'read)
                  (eq? op 'vector-set!))
       (si-exp stmt (Reg 'rax))]

      [(Collect (Int n))
       (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
             (Instr 'movq (list (Imm n) (Reg 'rsi)))
             (Callq 'collect 2))]
              
      [else (error "expected a stmt for si-stmt, instead got" stmt)])))

; si-exp : exp Location -> [Listof x86-instr]
(define si-exp
  (λ (exp arg)
    (match exp
      [(Prim 'any-vector-length `(,atm1))
       (define arg1 (si-atm atm1))
       (list (Instr 'movq (list (Imm -8) (Reg 'r11)))
             (Instr 'andq (list arg1 (Reg 'r11)))
             (Instr 'movq (Deref 'r11 0) (Reg 'r11))
              (Instr 'andq (list (Imm 126) (Reg 'r11)))
             (Instr 'sarq (list (Imm 1) (Reg 'r11)))
             (Instr 'movq (list (Reg 'r11) arg)))]
      [(Prim 'any-vector-ref `(,atm1 ,atm2))
       (define arg1 (si-atm atm1))
       (define arg2 (si-atm atm2))
       (list (Instr 'movq (list (Imm -8) (Reg 'r11)))
             (Instr 'andq (list arg1 (Reg 'r11)))
             (Instr 'movq (list arg2 (Reg 'rax)))
             (Instr 'addq (list (Imm 1) (Reg 'rax)))
             (Instr 'imulq (list (Imm 8) (Reg 'rax))) 
             (Instr 'addq (list (Reg 'rax) (Reg 'r11)))
             (Instr 'movq (Deref 'r11 0) arg))]
      [(Prim 'any-vector-set! `(,tup ,n ,rhs))
       (define tup^ (si-atm tup))
       (define n^ (si-atm n))
       (define rhs^ (si-atm rhs))
       (list (Instr 'movq (list (Imm -8) (Reg 'r11)))
             (Instr 'andq (list tup^ (Reg 'r11))) ; r11 is now the address 
             (Instr 'movq (list n^ (Reg 'rax)))
             (Instr 'addq (list (Imm 1) (Reg 'rax)))
             (Instr 'imulq (list (Imm 8) (Reg 'rax))) ;; location to change in rax
             (Instr 'addq (list (Reg 'rax) (Reg 'r11)))
             (Instr 'movq rhs^ (Deref 'r11 0))
             (Instr 'movq (list (Imm 0) arg)))]
      [(Prim read '())
       (list (Callq 'read_int 0)
             (Instr 'movq (list (Reg 'rax) arg)))]
      [(Prim '- `(,atm))
       (list (Instr 'movq (list (si-atm atm)
                                arg))
             (Instr 'negq (list arg)))]
      [(Prim '+ `(,atm1 ,atm2))
       (list (Instr 'movq (list (si-atm atm1)
                                arg))
             (Instr 'addq (list (si-atm atm2)
                                arg)))]
      [(Prim '- `(,atm1 ,atm2))
       (list (Instr 'movq (list (si-atm atm1)
                                arg))
             (Instr 'subq (list (si-atm atm2)
                                arg)))]

      [(Prim 'vector-ref `(,tup-var ,n))
          (let ([tup-var^ (si-atm tup-var)])
            (list (Instr 'movq (list tup-var^ (Reg 'r11)))
                  (Instr 'movq (list (Deref 'r11 (* 8 (add1 (Int-value n))))
                                     arg))))]

      [(Prim 'vector-set! `(,tup ,n ,rhs))
       (let ([tup^ (si-atm tup)]
             [rhs^ (si-atm rhs)])
         (list (Instr 'movq (list tup^ (Reg 'r11)))
               (Instr 'movq (list rhs^ (Deref 'r11 (* 8 (add1 (Int-value n))))))
               (Instr 'movq (list (Imm 0) arg))))]

      [(Prim 'vector-length `(,tup))
       (let ([tup^ (si-atm tup)])
         (list (Instr 'movq (list tup^ (Reg 'r11)))
               (Instr 'movq (list (Deref 'r11 0) arg))
               (Instr 'andq (list (Imm 126) arg))
               (Instr 'sarq (list (Imm 1) arg))))]

      [(Prim 'not `(,atm1))
       (let ([arg1 (si-atm atm1)])
         (list (Instr 'movq (list arg1 arg))
               (Instr 'xorq (list (Imm 1) arg))))]

      [(Prim op `(,atm1 ,atm2))
       #:when (cmp? op)
       (let ([arg1 (si-atm atm1)]
             [arg2 (si-atm atm2)]
             [cc (set-suffix op)])
         (list (Instr 'cmpq (list arg2 arg1))
               (Instr 'set (list cc (ByteReg 'al)))
               (Instr 'movzbq (list (ByteReg 'al) arg))))]

      [(GlobalValue y)
       (list (Instr 'movq (list (Global y) arg)))]

      [(Allocate n t)
       (define tag (Imm (compute-tag (cdr t))))
       (list (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
             (Instr 'addq (list (Imm (* 8 (add1 n))) (Global 'free_ptr)))
             (Instr 'movq (list tag (Deref 'r11 0)))
             (Instr 'movq (list (Reg 'r11) arg)))]

      [(FunRef f)
       (list (Instr 'leaq (list (FunRef f) arg)))]

      [(Call f params)
       (append (si-call-params params 0)
               (list (IndirectCallq f (length params))
                     (Instr 'movq (list (Reg 'rax) arg))))]
                                  
      [else (list (Instr 'movq (list (si-atm exp) arg)))])))

; si-call-params : [Listof Atm] Integer -> [Listof Instr]
(define (si-call-params loa i)
  (cond
    [(empty? loa) '()]
    [else (cons (Instr 'movq
                       (list (si-atm (car loa))
                             (Reg (vector-ref param-regs i))))
                (si-call-params (cdr loa) (add1 i)))]))

;; select-instructions : CFun -> pseudo-x86
(define (select-instructions p)
  (match-let ([(ProgramDefs types defs) (type-check-Cany p)])
    (define new-defs
      (for/list ([def defs])
        (match def
          [(Def f params rt info blocks)
           (define start-label (symbol-append f 'start))
           (define new-start
             (cons start-label
                   (new-start-block (dict-ref blocks start-label)
                                    params
                                    f)))
           (define new-blocks
             (for/list ([label-block blocks]
                        #:unless (eq? (car label-block) start-label)) ; don't redo start block
               (match-let ([(cons label tail) label-block])
                 (cons label (Block '() (si-tail f tail))))))
           (define new-blocks^
             (cons new-start new-blocks))
           (define new-info
             (dict-set info 'num-params (length params)))
           (Def f '() 'Integer new-info new-blocks^)])))
    (ProgramDefs types new-defs)))
             
         

; new-start-block : C-tail [Listof [Symbol : Type]] Symbol -> X86-Block
; opposite of args->locals, happens at beginning of start block (after prelude)
(define (new-start-block tail params label)
  (Block '()
         (append (args->locals (map (λ (x) (Var x))
                                    (map car params))
                               0)
                 (si-tail label tail))))

; args->locals : [Listof Var] Integer -> [Listof instr]
; opposite of new-start-block, happens before call
(define (args->locals args i)
  (cond
    [(empty? args) '()]
    [else
     (cons (Instr 'movq
                  (list (Reg (vector-ref param-regs i))
                        (car args)))
           (args->locals (cdr args) (add1 i)))]))

(define param-regs
  (vector 'rdi 'rsi 'rdx 'rcx 'r8 'r9))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; liveness analysis

; now contains liveness for all of a block's insturctions, not just Lbefore
(define label->live
  (make-hash))

; uncover-lives : x86Program -> x86Program
(define (uncover-lives p)
  (match p
    [(ProgramDefs info defs)
     (define defs^
       (for/list ([def defs])
         (match def
           [(Def f '() 'Integer info labels-blocks)
            ; initialize label->live
            (hash-clear! label->live)
            (for ([label (map car labels-blocks)])
              (hash-set! label->live label (list (set))))
            (hash-set! label->live
                       (symbol-append f 'conclusion)
                       (list (set (Reg 'rax) (Reg 'rsp))))

            (define bg (block-graph labels-blocks))
            (analyze-dataflow bg (transfer labels-blocks) (set) set-union f)

            (define blocks^
              (for/list ([label-block labels-blocks])
               (match label-block
                 [(cons label (Block binfo loi))
                  (define lives (uncover-live-loi loi))
                  (cons label
                        (Block (dict-set binfo 'lives lives)
                               loi))])))

            (Def f '() 'Integer info blocks^)])))
     
     (ProgramDefs info defs^)]))

; analyze-dataflow : Graph Funciton Bottom Function Label -> [Dictionaryof label live-before]
(define (analyze-dataflow G transfer bottom join name)
  (define mapping (make-hash))
  (remove-vertex! G (symbol-append name 'conclusion))
  (for ([v (in-vertices G)])
    (dict-set! mapping v bottom))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
         (define node (dequeue! worklist))
         (define input (for/fold ([state bottom])
                                 ([pred (in-neighbors trans-G node)])
                         (join state (dict-ref mapping pred))))
         (define output (transfer node input))
         (cond [(not (equal? output (dict-ref mapping node)))
                (dict-set! mapping node output)
                (for ([v (in-neighbors G node)])
                  (enqueue! worklist v))]))
  mapping)

; transfer : [DictionaryOf label Block] -> [label [Setof arg] -> [Setof arg]]
(define (transfer blocks)
  (λ (label live-after)
    (let ([block (dict-ref blocks label)])
      (match block
        [(Block binfo loi)
         (define lives
           (for/foldr ([acc (list live-after)])
                      ([instr loi])
               (cons (set-union 
                      (set-subtract (car acc)
                                    (locations-written instr))
                      (locations-read instr))
                     acc)))
         (hash-set! label->live label lives)
         (car lives)] ; return live before

        [else (error "transfer expected a block, got" block)]))))

; block-graph : [Listof [Pair label Block]] -> [DirectedGraph label label]
; returns graph of blocks according to their jumps
(define (block-graph blocks)
  (define edge-list (make-hash))
  (for ([b blocks])
    (match b
      [(cons label (Block binfo loi))
       (for/list ([instr loi]
                  #:when (or (Jmp? instr)
                             (JmpIf? instr)))
         (match instr
           [(Jmp label^)
            (hash-set! edge-list
                       (gensym 'tmp)
                       (list label label^))]
           [(JmpIf cc label^)
            (hash-set! edge-list
                       (gensym 'tmp)
                       (list label label^))]
           [else (void)]))]
      [else (error "expected block in block-interference, got" b)]))
  (make-multigraph (hash-values edge-list)))

; uncover-live-loi : [Listof instr] [Set arg] -> [Listof [Setof arg]]
; returns list of live-after sets
(define (uncover-live-loi loi) ; ila = initial live after
  (foldr
   (λ (instr acc)
     (cons (set-union
            (set-subtract
             (car acc)
             (locations-written instr))
            (locations-read instr))
           acc))
   (list (set))
   loi))

; locations-read : instr -> [Setof arg]
(define (locations-read instr)
  (match instr
    [(Instr op `(,arg1 ,arg2)) ; read 1st
     #:when (or (eq? op 'movq)
                (eq? op 'movzbq)
                (eq? op 'leaq))
     (locations-arg arg1)]
    [(Instr 'set `(,cc ,arg)) ; reads neither
     (set)]
    [(Instr op `(,arg1 ,arg2)) ; add/subtract/cmp/xorq (read both)
     #:when (or (eq? op 'addq)
                (eq? op 'subq)
                (eq? op
                (eq? op 'cmpq)
                (eq? op 'xorq))
     (set-union (locations-arg arg1)
                (locations-arg arg2))]
    [(Instr op `(,arg)) ; negq, popq, pushq
     (locations-arg arg)]
    [(Callq label arity) ; !!!!!!!!!
     (set-union (locations-arg label)
                (locations-call (vector->list param-regs)
                                arity))]
    [(IndirectCallq label arity)
     (set-union (locations-arg label)
                (locations-call (vector->list param-regs)
                                arity))]
    [(TailJmp label arity)
     (set-union (locations-arg label)
                (locations-call (vector->list param-regs)
                                arity))]
    [(Retq)
     (set)]
    [(Jmp label)
     (car (dict-ref label->live label))] ; beginning of the block
    [(JmpIf cc label)
     (car (dict-ref label->live label))])) ; beginning of the block

; locations-written : instr -> [Set arg]
(define (locations-written instr)
  (match instr
    [(Instr 'cmpq `(,arg1 ,arg2)) ; read, read
     (set)]
    [(Instr 'movzbq `(,arg1 ,arg2)) ; write to rax
     (set (Reg 'rax))]
    [(Instr op `(,arg1 ,arg2)) ; write 2nd
     #:when (or (eq? op 'addq)
                (eq? op 'subq)
                (eq? op 'movq)
                (eq? op 'xorq)
                (eq? op 'set)
                (eq? op 'leaq))
     (locations-arg arg2)]
    [(Instr 'negq `(,arg)) ; write
     (locations-arg arg)]
    ((Instr push/pop `(,arg)) ; read
     (set))
    [(Callq label arity)
     caller-save]
    [(IndirectCallq label arity)
     caller-save]
    [(TailJmp label arity)
     caller-save] 
    [(Retq) (set)]
    [(Jmp label) (set)]
    [(JmpIf cc label) (set)]))

; locations-arg : arg -> [Set arg]
(define (locations-arg arg)
  (match arg
    [(Imm int) (set)]
    [(FunRef f) (set)] ; ?
    [else (set arg)]))

; locations-call : [Listof Register] Integer -> [Set arg]
(define (locations-call regs arity)
  (cond
    [(= arity 0) (set)]
    [else (set-union (set (Reg (car regs)))
                     (locations-call (cdr regs)
                                     (sub1 arity)))]))

;(locations-call (list 'rax 'rbx 'rcx 'rdx 'rsp 'rbp 'rdi 'rsi 'r8 'r9) 8)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; build interference graph

;; build-inter-graph : x86Global -> x86Global
(define (build-inter-graph p)
  (match p
    [(ProgramDefs info defs)
     (define defs^
       (for/list ([def defs])
         (match def
           [(Def f '() 'Integer binfo blocks)
            (define locals (dict-ref binfo 'locals-types))
            (define edges (foldr (λ (pair rest)
                                   (append (match (cdr pair)
                                             [(Block binfo instructions)
                                              (bi instructions
                                                  (cdr (dict-ref binfo 'lives))
                                                  locals)])
                                           rest))
                                 '() blocks))
            (define graph (undirected-graph edges))
            (for/list ([local (map car locals)])
              (add-vertex! graph (Var local)))
            (define info-remove-label-live
              (dict-remove binfo 'label->live))
            (define blocks^ ;; remove liveness in info
              (for/list ([pair blocks])
                (cons (car pair)
                      (match (cdr pair)
                        [(Block binfo instrs)
                         (Block '() instrs)]))))
            (define binfo^
              (dict-set info-remove-label-live 'conflicts graph))
            (Def f '() 'Integer binfo^ blocks^)])))
     (ProgramDefs info defs^)]))

;; bi : [ListOf Instructions] [ListOf [SetOf Location]] [Listof Type] -> [ListOf Edge]
(define (bi loi los lot)
  (cond
    [(empty? loi) empty]
    [else (append
           (match (car loi)
             [(Callq 'collect int)
              (define lives (filter Var? (set->list (car los))))
              (for/foldr ([node lives])
                ([acc '()])
                (match (dict-ref (Var-name node) lot)
                  [(cons Vector types)
                   (append (map (λ (dest)
                                  (list node dest))
                                (set->list (set-union available-caller
                                                      available-callee)))
                           acc)]
                  [else acc]))] ; assuming call-live non-tuples are not overwritten
             [(Callq label int) ; read_int
              (foldr (λ (reg rest)
                       (append (map (λ (loc)
                                      (list reg loc))
                                    (set->list (car los)))
                               rest))
                     '()
                     (set->list available-caller))]
             [(IndirectCallq label n)
              (define lives (filter Var? (set->list (car los))))
              (for/foldr ([node lives])
                ([acc '()])
                (match (dict-ref (Var-name node) lot)
                  [(cons Vector types)
                   (append (map (λ (dest)
                                  (list node dest))
                                (set->list (set-union available-caller
                                                      available-callee)))
                           acc)]
                  [else acc]))] ; assuming call-live non-tuples are not overwritten
             [(TailJmp label n)
              (define lives (filter Var? (set->list (car los))))
              (for/foldr ([node lives])
                ([acc '()])
                (match (dict-ref (Var-name node) lot)
                  [(cons Vector types)
                   (append (map (λ (dest)
                                  (list node dest))
                                (set->list (set-union available-caller
                                                      available-callee)))
                           acc)]
                  [else acc]))] ; assuming call-live non-tuples are not overwritten
             [else
              (filter (λ (e) (not (equal? 0 e)))
                      (map (λ (loc) (bi-single (car loi) loc))
                           (set->list (car los))))])
           (bi (cdr loi) (cdr los) lot))]))

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
                  (eq? op 'movzbq)
                  (eq? op 'leaq))
       (let ([notSource (not (equal? loc arg1))]
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; allocate registers

(define pre-coloring
  (λ (loreg n)
    (cond
      [(empty? loreg) empty]
      [else (dict-set (pre-coloring (cdr loreg) (add1 n)) (car loreg) n)])))

(define available-caller
  (set (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10)))

(define available-callee
  (set (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))

; init-satur-list : [ListOf Var] Graph [DictionaryOf Reg Number(Color)] -> [SetOf Color]
(define (init-satur-list var g dict)
  (foldr (λ (pair rest)
           (cond
             [(list? (member (car pair) (sequence->list (in-neighbors g var))))
              (set-union (set (cdr pair)) rest)]
             [else rest])) 
         (set) 
         dict))

(define pre-color (append
                   (list (cons (Reg 'rax) -1)
                         (cons (Reg 'rsp) -2)
                         (cons (Reg 'r11) -3)
                         (cons (Reg 'r15) -4)
                         (cons (Global 'fromspace_end) -5)
                         (cons (Global 'free_ptr) -6))
                   (pre-coloring (set->list available-caller) 0)
                   (pre-coloring (set->list available-callee) (length (set->list available-caller)))))

;; allocate-registers : pseudo-x86 -> x86
(define (allocate-registers p)
  (match p
    [(ProgramDefs info defs)
     (define defs^
       (for/list ([def defs])
         (match def
           [(Def f '() 'Integer info blocks)
            (define graph (dict-ref info 'conflicts))
            (define types (dict-ref info 'locals-types))
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
                                                            ; weifeng: (Deref 'r15 int), the int field
                                                            ; is no longer affected by used-callees
                                            [else pr]))) var-mapping))
            (define num-normal-spill (num-normal-spilled (set->list (list->set (map cdr var-mapping)))))
            (define num-root-spill (num-root-spilled (set->list (list->set (map cdr var-mapping)))))
            (define info^ (dict-set* (dict-remove info 'conflicts)
                                     'color (append pre-color color-mapping)
                                     'home var-mapping^
                                     'used-callee used-callee
                                     'num-normal-spills num-normal-spill
                                     'num-root-spills num-root-spill))
            (define newblocks
              (for/list ([pair blocks])
                (define label (car pair))
                (define block (cdr pair))
                (define new-instrs
                  (match block
                    [(Block binfo instrs)
                     (assign-homes-instrs instrs var-mapping^)]))
                (cons label (Block '() new-instrs))))
            (Def f '() 'Integer info^ newblocks)])))
     (ProgramDefs info defs^)]))

; An Arg is one of :
; - (Reg Symbol) ;; Register
; - (Var Symbol) ;; Var
; - (Imm Number) ;; Imm

; is-reg? : Arg -> Boolean
(define (is-reg? a)
  (match a
    [(Reg reg) true]
    [else false]))


; ar-graph : Graph -> [DictionaryOf Var Number(Color)]
(define ar-vars ;; change [ListOf Color] to [SetOf Color] later
  (λ (g types)
    (let* ([var-satur-list (make-hash)] ;; [DictionaryOf Var [SetOf Color]]
           [var-handle-list (make-hash)];; [DictionaryOf Var Handle]
           [ls (sequence->list (in-vertices g))]
           [lovar (filter Var? ls)]) ; [Listof Var]
      (begin (for/list ([var ls]) ;; initialize var-satur-list
               (dict-set! var-satur-list var (init-satur-list var g pre-color)))
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
                           [else (begin
                                   (define var (pqueue-pop! pq))
                                   (define var-type (dict-ref types (Var-name var) #f))
                                   (define var-type^
                                     (match var-type
                                       [#f 'Integer] ; fix for var occurring uninitialized
                                       [else var-type]))
                                   (pqueue-decrease-key! pq (dict-ref var-handle-list var))
                                   (define sat-set (dict-ref var-satur-list var)) ;; [SetOf Color(Number)]
                                   (define index
                                     (match var-type^
                                       [(cons 'Vector rest)
                                        (find-index sat-set 0 10)]
                                       [else
                                        (find-index sat-set 0 11)]))
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
        #;(equal? (Reg 'r15) r))))

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

; map-to-loc : [PairOf Var Number] -> Location
(define (map-to-loc pr)
  (let* ([var (car pr)]
         [n (cdr pr)])
    (cond
      [(< n (+ (set-count available-caller)
               (set-count available-callee)))
       (find-ith n pre-color)]
      [else ; spill
       (if (odd? n) (Deref 'rbp (* (ceiling  (/ (- n 10) 2)) -8))
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

; assign-homes-single : Instr [ListOf [PairOf Symbol (Deref reg int)]] -> Instr
(define (assign-homes-single instr alist)
  (match instr
    [(Instr op `,ls)
     (Instr op (map (λ (arg)
                      (match arg
                        [(Var var) (dict-ref alist arg)]
                        [else arg]))
                    ls))]
    [(TailJmp f n)
     (define f-home
       (match f
         [(Var x) (dict-ref alist f)]
         [else f]))
     (TailJmp f-home n)]
    [(IndirectCallq f n)
     (define f-home
       (match f
         [(Var x) (dict-ref alist f)]
         [else f]))
     (IndirectCallq f-home n)]
    [else instr]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; patch instructions

;; patch-instructions : x86 -> x86
(define (patch-instructions p)
  (match p
    [(ProgramDefs info defs)
     (define defs^
       (for/list ([def defs])
         (match def
           [(Def f '() 'Integer info blocks)
            (define new-blocks
              (for/list ([block blocks])
                (define instrs-after-removing-duplicate
                  (match (cdr block)
                    [(Block binfo instructions)
                     (foldr (λ (instr rest)
                              (match instr
                                [(Instr 'movq `(,arg1 ,arg2))
                                 (if (equal? arg1 arg2)
                                     rest ;; remove instrs in case of (movq rbx, rbx)
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

                (define instrs-leaq-tailjmp
                  (foldr (λ (instr rest)
                           (let ([new-instrs
                                  (match instr
                                    [(Instr 'leaq `(,arg1 ,arg2))
                                     #:when (not (Reg? arg2))
                                     (list (Instr 'leaq (list arg1 (Reg 'rax)))
                                           (Instr 'movq (list (Reg 'rax) arg2)))]
                                    [(TailJmp f n)
                                     #:when (not (equal? f (Reg 'rax)))
                                     (list (Instr 'movq (list f (Reg 'rax)))
                                           (TailJmp (Reg 'rax) n))]
                                    [_ (list instr)])])
                             (append new-instrs rest)))
                         '() instrs-handling-cmpq-movzbq))
                
                (cons (car block)
                      (Block '() instrs-leaq-tailjmp))))

            (define info^
              (dict-remove (dict-remove (dict-remove info
                                                     'home)
                                        'color)
                           'locals-types)) ; these fields no longer needed
            
            (Def f '() 'Integer info^ new-blocks)])))
     
     (ProgramDefs info defs^)]))

; patch-instructions-instr : Instr -> [ListOf Instr]
(define (patch-instructions-instr instr)
  (match instr
    [(Instr op `(,arg1 ,arg2))
     (cond
       [(both-memory? (list arg1 arg2))
        (list (Instr 'movq (list  arg1 (Reg 'rax)))
              (Instr op (list (Reg 'rax) arg2)))]
       [else (list instr)])]
    [else (list instr)]))

; both-memory? : [ListOf Arg] -> Boolean
(define (both-memory? loa)
  (foldr (λ (a rest) (match a
                       [(Deref reg int) rest]
                       [(Global x) rest]
                       [else false]))
         true
         loa))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; p&c

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(ProgramDefs pinfo defs)
     (define labels-blocks
       (for/foldr ([acc '()])
                  ([def defs])
         (match def
           [(Def f '() 'Integer dinfo blocks)
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
         [spills (dict-ref info 'num-normal-spills)])
    (Imm (- (align (+ (* 8 callees) (* 8 spills)) 16) (* 8 callees)))))

; build-conclusion : info Symbol -> (cons label Block)
(define (build-conclusion info f)
  (let ([setup
         (append (list (Instr 'subq (list (Imm (* 8 (dict-ref info 'num-root-spills))) (Reg 'r15)))
                       (Instr 'addq (list (compute-rsp info) (Reg 'rsp))))
                 (foldl (λ (s rest) (cons (Instr 'popq (list s)) rest))
                        (list (Instr 'popq (list (Reg 'rbp)))
                              (Retq))
                        (set->list (dict-ref info 'used-callee))))])
    (cons (symbol-append f 'conclusion) (Block '() setup))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Define the compiler passes to be used by interp-tests and the grader 
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("shrink" ,shrink ,interp-Ldyn-prog)
    ("uniquify" ,uniquify ,interp-Ldyn-prog)
    ("reveal functions" ,reveal-functions ,interp-Ldyn-prog)
    ("insert casts" ,insert-casts ,interp-Lany)
    ("reveal casts" ,reveal-casts ,interp-Lany-prime)
    ("limit functions" ,limit-functions ,interp-Lany-prime ,type-check-Lany)
    ("expose allocation" ,expose-allocation ,interp-Lany-prime)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lany-prime)
;    ("explicate control" ,explicate-control ,interp-Cfun)
;    ("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
;    ("liveness analysis" ,uncover-lives ,interp-pseudo-x86-3)
;    ("build interference graph" ,build-inter-graph ,interp-pseudo-x86-3)
;    ("allocate registers" ,allocate-registers ,interp-x86-3)
;    ("patch instructions" ,patch-instructions ,interp-x86-3)
;    ("prelude-and-conclusion" ,prelude-and-conclusion #f)
    ))
