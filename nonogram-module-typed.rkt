#lang typed/racket

;;Programmer: Yuval Lando

;Uncomment for debug
;(require racket/fixnum)
;(require (only-in racket/future future touch))

;Run faster unsafe. comment for debuging
(require racket/require (for-syntax racket/base)
         (filtered-in (λ (name) (regexp-replace #rx"unsafe-" name ""))
                      racket/unsafe/ops)
         (only-in racket/future future touch))

(require/typed racket/future
   (processor-count (-> Integer)))

;;The board contain a list of list of numbers that represent the cols and rows in col-lst and row-lst
;;It also contain the known and unknown square in two 2d arrays
;;col is a list of columns and row is a list of rows
(struct: board ((cols : (Vectorof (Vectorof Integer))) 
                (rows : (Vectorof (Vectorof Integer))) 
                (col-lst : (Listof (Listof Integer))) 
                (row-lst : (Listof (Listof Integer)))))

(provide EMPTY FULL UNKNOWN UNINITIALIZE board-cols board-rows solve-cols solve-rows make-board finish?)

;;Posible square values 
(define EMPTY 0)
(define FULL 1)
(define UNKNOWN 2)
(define UNINITIALIZE 3)

(: make-board : (Listof (Listof Integer)) (Listof (Listof Integer)) -> board)
(define (make-board col-lst row-lst)
  (let*: 
       ([col-size (length col-lst)]
        [row-size (length row-lst)]
        [b (board 
             (build-vector col-size (lambda (ignore) (make-vector row-size UNKNOWN)))
             (build-vector row-size (lambda (ignore) (make-vector col-size UNKNOWN)))
             col-lst 
             row-lst)])
    b))

;;Fill a square in the board with a given square value.
(: fill-square! : Integer Integer Integer board -> Void)
(define (fill-square! x y sq board)
  (vector-set! (vector-ref (board-cols board) x) y sq)
  (vector-set! (vector-ref (board-rows board) y) x sq))

;;Fill a vector in a range with a given square value.
(: fill-vector! : (Vectorof Integer) Integer Integer Integer -> Void)
(define (fill-vector! vec start end sq)
  (for ([i (in-range start end)])
    (vector-set! vec i sq)))

;;Check if the vector is empty in the given range.
(: not-empty-vector-range? : (Vectorof Integer) Integer Integer -> Boolean)
(define (not-empty-vector-range? vec start end)
  (not
   (for/or: : Boolean ([i : Integer (in-range start end)])
     (fx= (vector-ref vec i) EMPTY))))

;;Check if the vector is full in a given range.
(: not-full-vector-range? : (Vectorof Integer) Integer Integer -> Boolean)
(define (not-full-vector-range? vec start end)
  (not
   (for/or: : Boolean ([i : Integer (in-range start end)])
     (fx= (vector-ref vec i) FULL))))

;;Return the last empty square in the vector vec in a given range from "start" to "end".
(: last-empty : (Vectorof Integer) Integer Integer -> Integer)
(define (last-empty vec start end)
  (let ([pos (for/or: : (U Integer False) ([i : Integer (in-range (fx- end 1) (fx- start 1) -1)]) 
               (if (fx= (vector-ref vec i) EMPTY) 
                   i 
                   #f))])
    (if pos 
        pos 
        -1)))

;;Replace the square of the vector vec with sq1 value by sq2 value. 
(: replace-vector! : (Vectorof Integer) Integer Integer -> Void)
(define (replace-vector! vec sq1 sq2)
  (for ([i (in-range (vector-length vec))])
    (when (fx= (vector-ref vec i) sq1)
      (vector-set! vec i sq2))))

;;vec is a one arrangment of row/column posibility.
;;common-vec store the square with the same value of all the posibilities on a row/column.
;;update-common! update common-vec with the arrangment possibility of vec.
(: update-common! : (Vectorof Integer) (Vectorof Integer) -> Void)
(define (update-common! vec common-vec) 
  (for ([i (in-range (vector-length common-vec))])
    (let ([x (vector-ref common-vec i)])
      (cond
        ((fx= x UNINITIALIZE) (vector-set! common-vec i (vector-ref vec i)))
        ((fx= x EMPTY) (when (fx= (vector-ref vec i) FULL) (vector-set! common-vec i UNKNOWN)))
        ((fx= x FULL) (when (fx= (vector-ref vec i) EMPTY) (vector-set! common-vec i UNKNOWN)))))))

;;A vector that represent a 2d array "seqs X space" where the seqs is the number of objects and space is the size of the space they can move. 
(: cost-vec : (Vectorof Integer))
(define cost-vec (make-vector (* (+ 30 1) (+ 8 1)) 0))

(: cost-set! : (Vectorof Integer) Integer Integer Integer -> Void)
(define (cost-set! vec seqs space val)
  (vector-set! vec (+ (* seqs (+ 30 1)) space) val))

;;Given the number of objects and the space that the object can move
;;It return the number of possiblities the progran has to check.
(: cost-ref : (Vectorof Integer) Integer Integer -> Integer)
(define (cost-ref vec seqs space)
  (vector-ref vec (+ (* seqs (+ 30 1)) space))) 

(: init-cost : (Vectorof Integer) -> Void)
(define (init-cost vec)
  (for ([i (in-range 0 (+ 8 1))])
    (cost-set! vec i 0 1))
  (for ([i (in-range 0 (+ 30 1))])
    (cost-set! vec 0 i 1))
  (for*: : Void 
        ([i : Integer (in-range 1 (+ 8 1))]
         [j : Integer(in-range 1 (+ 30 1))])
    (cost-set! vec i j (+ (cost-ref vec (- i 1) j) (cost-ref vec i (- j 1))))))

(init-cost cost-vec)

;;Check every arrangment of row/collumn sequences in lst
;;that are consistence with known data from test vector.
;;temp-vec is a temporary place to put a possibility in.
;;check-every-possibility return the square with the same value
;;for every arrangment in common-vec.
(: check-every-possibility : (Listof Integer) (Vectorof Integer) (Vectorof Integer) (Vectorof Integer) Integer -> Void)
(define (check-every-possibility lst test temp-vec common-vec turn)
  (: helper : (Listof Integer) Integer Integer -> Void)
  (define (helper lst pos space)
    (if (null? lst)
        (begin
          (when (not-full-vector-range? test pos (vector-length test))
            (fill-vector! temp-vec pos (vector-length test) EMPTY)
            (update-common! temp-vec common-vec)))
        (let ([pos+car (fx+ pos (car lst))]
              [pos-1 (fx- pos 1)])
          (let ([empty-pos (last-empty test pos pos+car)])
            (if (fx> empty-pos -1)
                (when (not-full-vector-range? test pos empty-pos)
                  (fill-vector! temp-vec pos (fx+ empty-pos 1) EMPTY)
                  (helper lst (fx+ empty-pos 1) (fx- space (fx+ (fx- empty-pos pos) 1))))
                (let loop ([i 0])
                  (when (<= i space) 
                    (if (fx> i 0)
                      (vector-set! temp-vec (fx+ pos-1 i) EMPTY)
                      (fill-vector! temp-vec (fx+ pos i) (fx+ pos+car i) FULL))
                    (if (not (fx= (vector-ref test (fx- (fx+ pos+car i) 1)) EMPTY))
                        (begin
                          (vector-set! temp-vec (fx- (fx+ pos+car i) 1) FULL)
                          (if (null? (cdr lst))
                              (helper (cdr lst) (fx+ pos+car i) (fx- space i))
                              (unless (fx= (vector-ref test (fx+ pos+car i)) FULL)
                                (vector-set! temp-vec (fx+ pos+car i) EMPTY)
                                (helper (cdr lst) (fx+ (fx+ pos+car i) 1) (fx- space i))))
                          (unless (fx= (vector-ref test (fx+ pos i)) FULL)
                            (loop (fx+ i 1))))
                        (when (not-full-vector-range? test (fx+ pos i) (fx- (fx+ pos+car i) 1))
                          (fill-vector! temp-vec (fx+ pos i) (fx+ pos+car i) EMPTY)
                          (helper lst (fx+ pos+car i) (fx- space (fx- (fx+ pos+car i) pos))))
                        ))))))))
  (let* ([seq-num (length lst)]
         [space (- (vector-length test) (+ (- seq-num 1) 
                                                 (apply + lst)))]
         [s (start-empty test)]
         [e (end-empty test)]
         [space-remain (- space s e)]
         [cost (cost-ref cost-vec seq-num space-remain)])
    ;;space is the number of squares in a row/column minus number of empty square between and the sum of squares
    (if (and (> cost (+ 2500 (* 2500 turn))) (< turn 5))
        (let ([space-remain (- space (count-empty test))])
          ;;It knows how to deal with the information
          (fill-vector! common-vec 0 (vector-length common-vec) UNKNOWN)
          ;;put every sequence in it's two extremes
          (let loop ([pos 0] [lst lst])
            (if (fx= (vector-ref test pos) EMPTY)
                (loop (+ pos 1) lst)
                (unless (null? lst)
                  (when (> (car lst) space-remain) 
                    (fill-vector! common-vec (+ pos space-remain) (+ pos (car lst)) FULL))
                  (loop (+ pos (car lst) 1) (cdr lst))))))  
        (begin
          (fill-vector! common-vec 0 (vector-length common-vec) UNINITIALIZE)
          (fill-vector! temp-vec 0 s EMPTY)
          (helper lst s (- space s e)))))) 

;;Put the information of common-vec to the column col of the board 
(: put-common-in-col : Integer (Vectorof Integer) board -> Void)
(define (put-common-in-col col common-vec board)
  (for ([i (in-range (vector-length common-vec))])
    (let ([x (vector-ref common-vec i)])
      (unless (fx= x UNKNOWN)
        (fill-square! col i x board)))))

;;Put the information of common-vec to the row "row" of the board 
(: put-common-in-row : Integer (Vectorof Integer) board -> Void)
(define (put-common-in-row row common-vec board)
  (for ([i (in-range (vector-length common-vec))])
    (let ([x (vector-ref common-vec i)])
      (unless (fx= x UNKNOWN)
        (fill-square! i row x board)))))


;;Check if the board is solved.
(: finish? : board -> Boolean)
(define (finish? board)
  (not 
   (for/or: : Boolean ([col : (Vectorof Integer) (in-vector (board-cols board))])
     (for/or: : Boolean ([e : Integer (in-vector col)]) (fx= e UNKNOWN)))))

;;Return the number of empty squares in the start of the vector
(: start-empty : (Vectorof Integer) -> Integer)
(define (start-empty vec)
  (let* ([len (vector-length vec)]
         [pos (for/or: : (U Integer False) 
                ([i (in-range 0 len)])
                (if (fx= (vector-ref  vec i) EMPTY)
                    #f
                    i))])
    (if pos
        pos
        len)))

;;Return the number of empty squares in the end of the vector with one exception
;;when the vector contain only empty squares it return 0. 
;;it is because the program add it to result of start-empty to check the number of empty squares.
(: end-empty : (Vectorof Integer) -> Integer)
(define (end-empty vec)
  (let* ([len (vector-length vec)]
         [pos (for/or: : (U Integer False) 
                ([i (in-range (- len 1) -1 -1)])
                (if (fx= (vector-ref vec i) EMPTY)
                    #f
                    i))])
    (if pos
        (- len pos 1)
        0)))

;;count empty square that are not one square in the middle
(: count-empty : (Vectorof Integer) -> Integer)
(define (count-empty vec) 
  (let ([len (vector-length vec)])
    (let loop ([i 0] [acc 0] [last EMPTY])
      (if (fx< i len)
        (if (fx= (vector-ref vec i) EMPTY)
            (loop (fx+ i 1) (fx+ acc (if (fx= last EMPTY) 1 0)) EMPTY)
            (loop (fx+ i 1) acc FULL))
        (fx+ acc (if (fx= (vector-ref vec (fx- len 1)) EMPTY) 1 0))))))

;;Count the number of empty square of a vec in a given range.
(: count-empty-range : (Vectorof Integer) Integer Integer -> Integer)
(define (count-empty-range vec start end)
  (for/sum: : Integer 
            ([i (in-range start end)])
           (if (fx= (vector-ref vec i) EMPTY)
               1
               0)))

;;Given a list and a number n it build a new list from the n,n*2,n*3 ... elements 
(: take-every-nth (All (A) (Listof A) Integer -> (Listof A)))
(define (take-every-nth lst n)
  (for/list ([e (in-list lst)] [i (in-naturals)] #:when (= (modulo i n) 0))
    e))

;;Try to use the multi core.
(: parallel-for : Integer ( Integer Integer Integer -> Void ) -> Void)
(define (parallel-for end fn)
  (let*: ([cores : Integer (processor-count)] 
          [fvec : (Vectorof (Futureof Void)) 
                (build-vector (- cores 1) (lambda (i) (future (lambda () (fn i end cores)))))])
    (fn (- cores 1) end cores)
    (for ([e (in-vector fvec)])
      (touch e))))

;;Calculate the number of possibilities need to check for a given vector for known values of row/col and list of size of object.
(: score : (Vectorof Integer) (Listof Integer) -> Integer)
(define (score test lst)
  (let* ([seq-num (length lst)]
         [space (- (vector-length test) (+ (- seq-num 1) 
                                              (apply + lst)))]
         [s (start-empty test)]
         [e (end-empty test)]
         [space-remain (- space s e)])
    (cost-ref cost-vec seq-num space-remain)))

;;I need it to bypass problems with typed racket.
(define integer-sort (inst sort (List Integer (Listof Integer) Integer) (List Integer (Listof Integer) Integer)))

;;cols and col-lst can also be rows and row-lst
;;It sort them out in order to divide the load between the cores.
(: lst-by-score : (Vectorof (Vectorof Integer)) (Listof (Listof Integer)) -> (Listof (List Integer (Listof Integer) Integer)))
(define (lst-by-score cols col-lst)
  (integer-sort
   (for/list: : (Listof (List Integer (Listof Integer) Integer))
     ([i : Integer (in-naturals)]  [v : (Vectorof Integer) (in-vector cols)] [e : (Listof Integer) (in-list col-lst)])
     (list i e (score v e)))
   (lambda: ((x : (List Integer (Listof Integer) Integer)) (y : (List Integer (Listof Integer) Integer)))
     (let ([e1 (caddr x)] [e2 (caddr y)]) (> e1 e2)))))

;One step in solving the problem checking every column one at a time.
(: solve-cols : board Integer -> Void)
(define (solve-cols board turn)
  (let ([temp-vec (make-vector (vector-length (board-rows board)))]
        [common-vec (make-vector (vector-length (board-rows board)) UNKNOWN)]
        [sorted-lst (lst-by-score (board-cols board) (board-col-lst board))])
    (parallel-for (vector-length (board-cols board))
        (lambda (start end by)
          (for ([col-num+lst (in-list (take-every-nth (drop sorted-lst start) by))])
            (let ([col-num (car col-num+lst)]
                  [lst (cadr col-num+lst)])
              (check-every-possibility lst (vector-ref (board-cols board) col-num) temp-vec common-vec turn)
              (put-common-in-col col-num common-vec board)))))))

;One step in solving the problem checking every row one at a time.
(: solve-rows : board Integer -> Void)
(define (solve-rows board turn)
  (let ([temp-vec (make-vector (vector-length (board-cols board)))]
        [common-vec (make-vector (vector-length (board-cols board)) UNKNOWN)]
        [sorted-lst (lst-by-score (board-rows board) (board-row-lst board))])
    (parallel-for (vector-length (board-rows board))
        (lambda (start end by)
          (for ([row-num+lst (in-list (take-every-nth (drop sorted-lst start) by))])
            (let ([row-num (car row-num+lst)]
                  [lst (cadr row-num+lst)])
              (check-every-possibility lst (vector-ref (board-rows board) row-num) temp-vec common-vec turn)
              (put-common-in-row row-num common-vec board)))))))

;;If i ever use typed racket again this is a useful badly documented property.
;;Casting in Typed racket
;; (define: x : Any 3)
;; (if (exact-integer? x) 
;;        (* x x))
;;        (error "x is not a number"))                
;; If you need to cast a complex data type you do
;; (define-type name type)
;; (define-predicate name? name)
;; (if (name? x)
;;     (do-some-thing x)
;;     (error "x is not a name"))

