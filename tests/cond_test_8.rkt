;#lang racket
(let ([x 3])
  (let ([y 4])
    (+ x (- y (if (not (eq? x y)) x y)))))
    