(let ([sum 0])
  (let ([m (read)])
    (let ([n (read)])
      (let ([i 1])
        (begin
          (while (<= i m)
            (let ([j 1])
              (begin
                (while (<= j n)
                  (begin
                    (set! sum (+ sum (+ i j)))
                    (set! j (+ j 1))
                    ))
                (set! i (+ i 1)))))
            sum)))))