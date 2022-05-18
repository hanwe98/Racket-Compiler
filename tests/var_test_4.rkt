(let ([x (let ([x 2])
           (+ x (let ([x 3])
                  x)))])
  x)