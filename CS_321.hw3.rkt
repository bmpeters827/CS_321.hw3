#lang plai
(define eight-principles
  (list "Know your rights."
        "Acknowledge your sources."
        "Protect your work."
        "Avoid suspicion."
        "Do your own work."
        "Never falsify a record or permit another person to do so."
        "Never fabricate data, citations, or experimental results."
        "Always tell the truth when discussing your work with your instructor."))


(define-type FAE
  [num (n number?)]
  [add (lhs FAE?) (rhs FAE?)]
  [sub (lhs FAE?) (rhs FAE?)]
  [id  (name symbol?)]
  [if0 (test FAE?) (then FAE?) (else FAE?)]
  [fun (param symbol?) (body FAE?)]
  [app (fun FAE?) (arg FAE?)])

(define-type FWAE
  [W-num (n number?)]
  [W-add (lhs FWAE?)
         (rhs FWAE?)]
  [W-sub (lhs FWAE?)
         (rhs FWAE?)]
  [W-with (name symbol?)
          (named-expr FWAE?)
          (body FWAE?)]
  [W-id (name symbol?)]
  [W-if0 (tst FWAE?)
         (thn FWAE?)
         (els FWAE?)]
  [W-fun (params (listof symbol?))
         (body FWAE?)]
  [W-app (fun-expr FWAE?)
         (arg-exprs (listof FWAE?))])

(define (check-pieces expression size what)
  (unless (and (list? expression)
               (= (length expression) size))
    (parse-error what expression)))
 
(define (parse-error what expression)
  (error 'parser
         "expected: ~a, found: ~a"
         what
         expression))

(define (parse exp)
  (cond
    [(number? exp) (W-num exp)]
    [(symbol? exp) (W-id exp)]
    [(and (list? exp) (not (empty? exp)))
     (case (first exp)
       [(+)
        (check-pieces exp 3 "add")
        (W-add (parse (list-ref exp 1))
               (parse (list-ref exp 2)))]
       [(-)
        (check-pieces exp 3 "sub")
        (W-sub (parse (list-ref exp 1))
               (parse (list-ref exp 2)))]
       [(with)
        (check-pieces exp 3 "with")
        (check-pieces (list-ref exp 1) 2 "with binder")
        (W-with (first (second exp))
                (parse (second (second exp)))
                (parse (third exp)))]
       [(if0)
            (check-pieces exp 4 "if0")
            (W-if0 (parse (second exp))
                   (parse (third exp))
                   (parse (fourth exp)))]
       [(fun)
        (check-pieces exp 3 "fun")
        (W-fun (second exp)
               (parse (third exp)))]
       [else
        (check-pieces (list (first exp)) 1 "app")
        (W-app (parse (first exp))
               (map parse (rest exp)))])]))

(test (symbol? 'f) true)

(test (parse '{+ 1 2}) (W-add (W-num 1) (W-num 2)))

(test (parse 1) (W-num 1))

(test (parse '{{fun {x} {+ x 1}} 10})
      (W-app (W-fun '{x} (W-add (W-id 'x) (W-num 1))) (list (W-num 10))))

(test (parse '{with {x 1} {+ x 2}})
      (W-with 'x (W-num 1) (W-add (W-id 'x) (W-num 2))))

(test (parse '(f x))
      (W-app (W-id 'f) (list (W-id 'x))))

(test (parse '(f x y))
      (W-app  (W-id 'f) (list (W-id 'x) (W-id 'y))))

(test (parse '(f x y z))
      (W-app (W-id 'f) (list (W-id 'x) (W-id 'y) (W-id 'z))))

(define (compile an-fwae)
  (type-case FWAE an-fwae
    [W-num (n) (num n)]
    [W-id (name) (id name)]
    [W-add (l r) (add (compile l) (compile r))]
    [W-sub (l r) (sub (compile l) (compile r))]
    ;need to look at b/c of param being (listof symbol?)
    [W-fun (param body) (if (empty? param)
                            (error "nullary function")
                            (fun
                             (first param)
                             (if (equal? 1 (length param))
                                 (compile body)
                                 (compile (W-fun (rest param) body)))))]
    ;need to look at b/c of arg being (listof FWAE?)
    [W-app (fun arg) (if (empty? arg)
                         (error "nullary application")
                         (app (if (equal? 1 (length arg))
                                  (compile fun)
                                  (compile (W-app fun (reverse (rest (reverse arg))))))
                              (compile (first (reverse arg)))))]
    [W-with (name bound-expr body)
            (app (fun name (compile body))
                 (compile bound-expr))]
    [W-if0 (tst thn els) (if0 (compile tst)
                              (compile thn)
                              (compile els))]))

(test (compile (parse '{{fun {x} {+ x 1}} 10}))
      (app (fun 'x (add (id 'x) (num 1))) (num 10)))

(test (compile (parse '{with {x 1} {+ x 2}}))
      (app (fun 'x (add (id 'x) (num 2))) (num 1)))

(test (compile (parse `{+ {fun {x} x} {1 2}}))
      (add (fun 'x (id 'x)) (app (num 1) (num 2))))

(test (compile (parse '(f x y)))
  (app (app (id 'f) (id 'x)) (id 'y)))

(test (compile (parse '(f x y z)))
      (app (app (app (id 'f) (id 'x)) (id 'y)) (id 'z)))


;BEGINNING OF INTERP FUNCTIONS

(define-type FAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body FAE?)
            (ds DefSub?)])

(define-type DefSub
  [mtSub]
  [aSub (name symbol?)
        (value FAE-Value?)
        (rest DefSub?)])

(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
 
(define num+ (num-op +))
(define num- (num-op -))

(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier: ~a" name)]
    [aSub (name2 value rest)
          (if (equal? name2 name)
              value
              (lookup name rest))]))

(define (interp a-fae ds)
  (type-case FAE a-fae
    [num (n) (if (number? n)
                 (numV n)
                 (error "expected number"))]
    [add (l r) (if
                (and (numV? (interp l ds)) (numV? (interp r ds)))
                   (num+ (interp l ds) (interp r ds))
                   (error "expected number"))]
    [sub (l r) (if (and (numV? (interp l ds)) (numV? (interp r ds)))
                   (num- (interp l ds) (interp r ds))
                   (error "expected number"))]
    [id (name) (lookup name ds)]
    [if0 (test then else) (if (equal? (numV 0) (interp test ds))
                              (interp then ds)
                              (interp else ds))]
    [fun (param-name body) (closureV param-name body ds)]
    [app (fun-expr arg-expr)
         (define fun-val (interp fun-expr ds))
         (if (numV? fun-val)
             (error "expected function")
             (interp (closureV-body fun-val)
                     (aSub (closureV-param-name fun-val)
                           (interp arg-expr ds)
                           (closureV-ds fun-val))))]))

(define (interp-expr an-fae)
  (type-case FAE-Value (interp an-fae (mtSub))
    [numV (n) n]
    [closureV (param body ds) 'function]))

(test/exn (interp-expr (compile (parse '(0 Q))))
          "expected function")

(test/exn (interp-expr (compile (parse `(1 2))))
          "expected function")

(test (interp-expr (num 10)) 10)

(test (interp-expr (fun 'x (id 'x))) 'function)

(test (interp-expr (compile (parse '(if0 0 1 2))))
      1)

(test (interp-expr (compile (parse '(if0 (if0 1 2 0) 4 5))))
      4)

(test (interp-expr (compile (parse '(if0 (if0 1 2 0) (if0 4 5 6) (if0 7 8 9)))))
      6)

;test fails

(test (interp-expr (compile (parse `(with (x 2) ((with (x 1) (fun (y) (+ x y))) x)))))
      3)

(test (interp-expr (compile (parse `(with (x (+ 1 2)) (+ x x)))))
      6)

(test (interp-expr (compile (parse `(with (x (+ 1 2)) (with (y (+ x x)) (+ y y))))))
      12)

(test (interp-expr (compile (parse `(with (x (+ 1 2)) (with (x (+ x x)) (+ x x))))))
      12)

(test (interp-expr
       (compile (parse `(with (x 2) (with (f (fun (y) (- x y))) (f 1))))))
      1)

(test (interp-expr (compile (parse `((fun (x y z) z) 1 2 3))))
      3)

;more test fails

(test/exn (interp-expr (compile (parse `(+ 1 (fun (x) x)))))
          "expected number")

(test/exn (interp-expr (compile (parse `(- (fun (x) x) 1))))
          "expected number")

(test/exn (compile (parse `(1)))
          "nullary application")

;(define multiply
;  '{with {help1 {fun {help1 x y} {if0 x 1 {if0 y 0 {help1 help1 {- x 1} {+ y 1}}}}}}
;         {with {neg? {fun {x} {help1 help1 x x}}}
;               {with {mult {fun {mult x y} {if0 {neg? y}
;                                                {- 0 {if0 {- 0 y} 0 {+ x {mult mult x {- {- 0 y} 1}}}}}
;                                                {if0 y 0 {+ x {mult mult x {- y 1}}}}}}}
;                     {fun {x y} (mult mult x y)}}}})

(define factorial
  `{with {help1 {fun {help1} {fun {x y} {if0 x 1 {if0 y 0 {help1 {- x 1} {+ y 1}}}}}}}
         {with {neg? {fun {x} {help1 x x}}}
               {with {mult {fun {mult x y} {if0 {neg? y}
                                                {- 0 {if0 {- 0 y} 0 {+ x {mult mult x {- {- 0 y} 1}}}}}
                                                {if0 y 0 {+ x {mult mult x {- y 1}}}}}}}
                     {with {fac {fun {fac x} {if0 x 1 {mult mult x {fac fac {- x 1}}}}}}
                           {fun {n} {fac fac n}}}}}})

;factorial failed tests

(test (interp-expr (compile (parse `(,factorial 2))))
      2)

(test (interp-expr (compile (parse `(,factorial 3))))
      6)

(test (interp-expr (compile (parse `(,factorial 4))))
      24)

(define prime?
  `{with {help1 {fun {help1 x y} {if0 x 1 {if0 y 0 {help1 help1 {- x 1} {+ y 1}}}}}}
         {with {neg? {fun {x} {help1 help1 x x}}}
               {with {mult {fun {mult x y} {if0 {neg? y}
                                                {- 0 {if0 {- 0 y} 0 {+ x {mult mult x {- {- 0 y} 1}}}}}
                                                {if0 y 0 {+ x {mult mult x {- y 1}}}}}}}
                     {with {check {fun {check x y plier} {if0 {- x y}
                                                              1
                                                              {if0 {- x {mult mult y plier}}
                                                                   0
                                                                   {if0 {neg? {- x {mult mult y plier}}}
                                                                        {check check x {+ y 1} 1}
                                                                        {check check x y {+ plier 1}}}}}}}
                           {fun {x}
                                ;it will do some function that checks if any multiple is equal to it
                                {if0 {check check x 2 1} 1 0}}}}}})

(test (interp-expr (compile (parse `(,prime? 2))))
      0)

(test (interp-expr (compile (parse `(,prime? 3))))
      0)

(test (interp-expr (compile (parse `(,prime? 4))))
      1)

(test (interp-expr (compile (parse `(,prime? 5))))
      0)

(test (interp-expr (compile (parse `(,prime? 6))))
      1)

(test (interp-expr (compile (parse `(,prime? 7))))
      0)

(test (interp-expr (compile (parse `(,prime? 8))))
      1)

(test (interp-expr (compile (parse `(,prime? 9))))
      1)

(test (interp-expr (compile (parse `(,prime? 10))))
      1)

(test (interp-expr (compile (parse `(,prime? 11))))
      0)

(test (interp-expr (compile (parse `(,prime? 12))))
      1)

(test (interp-expr (compile (parse `(,prime? 13))))
      0)

(test (interp-expr (compile (parse `(,prime? 14))))
      1)

(test (interp-expr (compile (parse `(,prime? 17))))
      0)

(test (interp-expr (compile (parse `(,prime? 19))))
      0)

(test (interp-expr (compile (parse `(,prime? 23))))
      0)