#lang slideshow

;;Programmer: Yuval Lando

(require "nonogram-module-typed.rkt"
         racket/fixnum)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Helper function for drawing the solution
(define (square size)
  (filled-rectangle size size))

(define (black-square size)
  (frame (colorize (square size) "black") #:color "black"))

(define (white-square size)
  (frame (colorize (square size) "white") #:color "black"))

(define (yellow-square size)
  (frame (colorize (square size) "yellow") #:color "black"))

(define (red-square size)
  (colorize (square size) "red"))

(define (red-line size sq-num)
  (apply hc-append
    (make-list sq-num (red-square size))))

(define (separator size sq-num)
  (apply hc-append
    (make-list sq-num (white-square size))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Helper function for show-solution
;;show one row in the solution
(define (show-row row)
  (apply hc-append
         (for/list ([x (in-vector row)]) 
           (cond
             ((= x FULL) (black-square 10))
             ((= x EMPTY) (white-square 10))
             (else (yellow-square 10))))))
  
;Show the state of the board
(define (show-solution board)
  (vc-append
   (red-line 10 (+ (vector-length (board-cols board)) 2))
   (apply vc-append
          (map
           (lambda (x)
             (hc-append (red-square 10) (show-row x) (red-square 10)))
           (vector->list (board-rows board))))
   (red-line 10 (+ (vector-length (board-cols board)) 2))))
      
;;;Show every step of the solution
(define (run cols rows)
  (define (show-solve-cols board turn)
    (solve-cols board turn)
    (show-solution board))
  (define (show-solve-rows board turn)
    (solve-rows board turn)
    (show-solution board))
  (let* ([board (make-board cols rows)]
         [sp-num (+ (vector-length (board-cols board)) 2)])
    (apply 
     vc-append
     (let loop ([pic-lst (list (show-solution board))] [turn 0])
       (if (finish? board)
           (reverse pic-lst)
           (let ([pic-lst2 (cons (show-solve-cols board turn) (cons (separator 10 sp-num) pic-lst))])
             (if (finish? board)
                 (reverse pic-lst2)
                 (let ([pic-lst3 (cons (show-solve-rows board turn) (cons (separator 10 sp-num) pic-lst2))])
                   (loop pic-lst3 (+ 1 turn))))))))))
;
;;;show only the end of the solution
(define (run2 cols rows)
  (let ([board (make-board cols rows)])
    (let loop ([turn 0])
      (unless (finish? board)
        (solve-cols board turn)
        (solve-rows board turn)
        (loop (+ 1 turn))))
    (show-solution board)))

;;Uncomment to try another puzzle           
(define *col-lst* 
  '((3 4) (5 6) (5 8) (6 8) (6 1 7) 
    (6 5 1 2) (6 3 2 3) (4 2 6) (3 3 4) (1 3 6) 
    (2 8) (2 8) (4 1 7) (2 7 2 1 2) (4 2 3) 
    (8 6) (10 4) (9) (9) (7)))
(define *row-lst*
  '((4 5) (7 8) (8 3 6) (8 2 1 6) (7 2 1 5)
    (7 2 1 5) (4 2 1 5) (2 1 5) (1 1 4) (2 1 3)
    (1 1) (2 1) (2 2 2 2) (7 7) (5 6 2)
    (5 6 2) (6 7 2) (5 7 3) (7 7) (5 5)))


;(define *col-lst*
;  '(() (2 1) (5 1) (7 2 1) (13 1)
;    (13 2) (1 13) (8 1) (1 4 1) (1)
;    (1 2 1) (7 1) (2 7 1) (11 2) (13 1)
;    (11 2) (10 1) (6 1) (1) (1)))
;(define *row-lst*
;  '((3) (5) (2 3) (2 6) (2 2 6)
;    (4 8) (5 8) (7 7) (8 6) (8 6)
;    (7 5) (6 3) (4 1 1) (3 1 1) (3 6)
;    (3 3 2) (2 3) (1 2) (2) (3)))


;(define *col-lst*
;  '((3) (5) (3 1) (3 1 5) (4 1 3 3)
;    (2 1 4 2) (3 1 1 1) (2 2 1 1) (2 2 1 1) (2 2 2 1)
;    (2 3 1 1) (6 4 1) (4 2 2 4 3) (3 2 1 4) (6 1 2)
;    (7 2 2 1) (4 4 1) (4 2) (7) (3)))
;;A list of numbers to the left of the nonogram puzzle
;(define *row-lst*
;  '((7) (10) (5 4) (4 9) (12 2)
;    (2 7) (2 5) (9 3) (1 4 2) (1 5)
;    (2 1) (1 2) (2 1 3) (1 1 5) (1 2 5)
;    (1 1 4) (2 1 1 1) (1 2 1 1) (2 1 1 2) (8 4)))


;(define *col-lst*
;  '((3 1 4 4) (3 6 1 2) (4 11 2) (3 7 1 2) (1 14 4)
;    (1 1 8 6 5) (3 4 10 1 1 1) (1 2 3 4 1) (3 3 1 1) (3 1 1 2)
;    (3 3 2 2) (4 3 1 4) (5 3 1 4) (12 1 1 4) (16 3)
;    (18 3 1) (5 6 3) (1 2 6 8) (1 1 1 1 7) (1 3 1 3 5)
;    (6 5 1) (7 4 7) (6 4 8) (1 6 4 1 7) (3 7 4 3)
;    (1 9 8) (3 1 5 7) (4 1 1 3 1 1 1 3) (6 1 1 4 1) (3 2 1 2 4 3)))
;(define *row-lst*
;  '((4 5 2 3) (1 5 1 4) (2 6 6) (8 3 3) (8 3 2)
;    (6 2 3 3) (3 3 4) (6 3 3 6 4) (7 3 3 5 1) (9 4 1 3 1)
;    (4 6 1 2) (3 9 2 1) (2 5 7) (3 4 7) (9 4 7)
;    (4 3 3 1 6) (10 1 1 1 1 1 2 4) (7 2 1 3) (7 4 2 3) (7 3 1 2)
;    (6 6 2) (1 3 7 4) (1 4 1 8 3) (2 1 10) (1 7) 
;    (2 1 6) (2 2 7 3 3) (1 11 8 1) (6 3 4 3) (7 3 4 1)))

;;This is the hardest puzzle. It takes 0.5 seconds compile and 4 second in interupt to be solved.
;(define *col-lst*
;  '((6 6 3) (20 1) (5 7 4 1) (5 4 6) (4 1 4 2)
;    (2 1 2 1 5) (4 2 3 2 2) (2 2 4 1 5) (2 5 4 2) (6 6)
;    (9 1 5 1) (3 4 1 2 4 1) (4 4 1 2 2) (3 4 1 1 3 1 1) (1 6 1 2 1 1)
;    (5 4 1 1 1 1 1) (5 4 1 2 1 1 2) (5 2 1 2 1 2) (5 2 1 1 1 2) (6 2 1 1 3)
;    (6 2 2 3) (6 1 2 4) (6 1 3 5) (5 1 5 5) (5 8 3 1)
;    (6 2) (5 10) (5 2 2 3 1) (10 2 2) (8 6)))
;(define *row-lst*
;  '((7) (2 8) (3 3 9) (5 3 9) (4 2 3 11)
;    (7 1 1 6) (4 1 1 4 4) (3 1 11 1) (2 1 15) (3 1 1 7 4)
;    (4 1 1 3 8) (4 1 10) (3 1 14) (3 3 7) (3 5 3 2)
;    (3 6 5 1 2) (2 8 2 1 2) (2 8 1 2) (2 4 2) (3 2 2)
;    (2 2 1 1) (2 1 1 1) (3 1 2 2) (2 2 2 1 5 1 3) (1 2 2 2 2 1 2)
;    (7 1 3 3 2 1) (11 1 3 2 1) (1 1 1 1 1 5 2 1) (7 9 2 2) (7 7 2 3)))

;(define *col-lst*
;  '((8 1 9) (3 3 8) (2 1 2 3 8) (2 1 2 1 1 1 2) (3 3 1 1 1 1 1 2)
;    (3 3 1 1 1 1 1 2) (3 1 2 1 1 2 1 3) (2 1 2 3 8) (3 3 8) (8 1 9)
;    (13) (2 12 1) (1 1 1 2 7 1) (7 2 4 2) (7 2 1)
;    (1 5 4 1) (1 1 1 1 1) (7 4 1 2) (2 2 1 1 2) (10 1 1 1)
;    (7 2 2) (1 5 8 2) (1 1 1 1) (8 2) (1 1 1 2)))
;(define *row-lst*
;  '((8) (10) (2 3 2) (1 1 5 5) (1 2 2 1 3 1 2 2)
;    (1 1 1 3 1 3 1) (1 2 1 1 3 1 3 1) (1 6 1 4 1 3 2) (1 6 1 3 1 3 1) (1 1 13)
;    (2 2 2 1) (12 1 1) (1 1 3 1 1) (4 4 1 1) (2 2 1 1)
;    (1 3 4 1) (13 1 1 1) (3 7 1 1 1) (3 2 7 1 1 1) (3 8 4)
;    (3 2 9 1) (3 8 4) (13) (11 1 2 2 2) (3 9)))

;(define *col-lst*
;  '((1) (2) (1 3) (2 4) (1 1 7 4)
;    (1 1 9 4) (1 2 11 3) (2 1 12 3) (1 2 3 9 2 5) (2 1 3 8 2 6)
;    (3 3 10 1 4) (7 4 3 1 2) (2 10 1 2 1 1) (2 1 7 1 2 1 1) (3 2 4 1 1)
;    (3 3 4 1 1) (2 3 4 1 1 1) (1 11 1 1) (9 1 1 1) (1 1)
;    (1 1) (1 1) (1 2) (1 2) (6)))
;(define *row-lst*
;  '((6) (1 3) (3 2 3) (3 1 6) (8)
;    (1) (3 1 3) (7 3) (8 3) (4 4 3)
;    (5 3 2) (6 2 2) (7 2 2) (7 2 2) (10 2)
;    (10 2) (8 3) (6 4) (4 3 6) (8 2 3)
;    (15) (12) (9) (8 1) (2 1 1 1)
;    (2 1) (3 1) (3 2) (3 2) (13)))

;(define *col-lst*
;  '((6) (2) (5 1 1) (8 1 1 1) (11 1 2 1)
;    (11 1 3 3) (11 1 1 1) (8 2 1 2) (6 1 1 2) (4 2 7)
;    (5 2 1 1 1 1 2) (5 2 1 1) (5 2 2 1 1 1) (6 1 1 4 1 1) (6 6 3)
;    (1 3 3 1 1 2) (1 1 2 1 2 2) (2 1 5 2) (4 6 2) (1 1 6 5 2)
;    (1 1 6 2) (1 1 3 4 3) (1 2 3 3) (15 4) (10 5)))
;(define *row-lst*
;  '((5) (11) (10 1) (11 6) (5 6 1 1)
;    (6 3 1 1) (6 2 2 1) (6 1 1 1) (6 2 1 4) (5 1 1 3)
;    (5 2 1 2) (7 1 1 2) (3 1 1 1 2) (1 2 1 4 1 1 2) (5 1 1 2)
;    (1 3 1 1 2) (1 3 4 1 1 2) (1 1 2 9 2) (3 2 1 1 7) (2 4 1 2 7)
;    (1 1 1 3 7 1) (1 1 1 1 6 2) (2 1 2 4) (6 11) (1 4 11)))


;(define *col-lst*
;  '((2 5 4 7) (1 1 5 5 2) (1 1 1 1 4 6) (1 1 1 5 2 3) (1 1 2 6 5)
;    (1 1 7 5) (2 2 5) (1 3 5) (1 8) (6 1 1 2)
;    (3 2) (6 2) (2 5 2) (2 2 1 2 2) (2 2 1 2 2)
;    (1 2 1 1 2 1 2) (3 1 1 2 4) (1 2 3) (3 1 1 3) (1 1 1 3)
;    (3 3 1 3) (1 1 2 3) (3 3 2 3) (1 1 3 4) (3 10)))
;(define *row-lst*
;  '((10 3 3) (1 1 1 2 1 1 1) (2 2 1 1 1 1 3 3) (1 1 1 1 1 1) (2 1 1 1 1 3 3)
;    (1 1 1 1 1) (7 1 4 3) (2 3 5 3) (4 1 1 3 2) (6 7 2)
;    (6 1 2 2 2) (4 1 3 1 1) (2 3 1 6 2) (3 1 3 2 1) (3 1 4 1)
;    (4 3 2 1) (3 2 2 1) (1 1 3 2 1) (1 1 2 2 1) (2 3 1 1)
;    (2 2 1 1) (1 3 1 2) (1 2 8) (1 2 9) (9)))


;(define *col-lst*
;  '((3 1) (5) (5 1) (1 6) (5 1)
;    (1 1) (1 6) (2 1 7) (2 2 9 1) (3 5 2 1)
;    (10 1) (9 1) (8 1) (7 1) (7 1)
;    (7 2) (7) (4) (2) (1)))
;(define *row-lst*
;  '((3) (7) (1 3) (1 2) (1 3)
;    (1 3) (1 4) (1 6) (8) (9)
;    (4 4) (3 4) (2 2 3) (1 2 2 4) (1 3 2 3)
;    (5 1 3) (5 1 3) (3 1 3) (1 1 1 5) (5 2 7)))
 

;(define *col-lst*
;  '((11) (7 3 1) (4 2 2) (3 1 1 2 3) (2 1 1 1 4)
;    (2 1 1 1 3 1) (2 1 2 1 2 1) (2 1 2 1) (2 5 1) (5 3)
;    (1 7) (15) (2 5 2) (2 1 1 1 2 1) (3 2 1 2 1)
;    (2 1 1 1 3 1) (3 1 1 4) (4 1 2) (6 2 1) (9)))
;(define *row-lst*
;  '((3 3) (6 5) (8 7) (3 3 3 3) (2 3 5 2 2)
;    (2 1 1 1 1 2) (2 1 1 1) (1 1 1 1 2 1) (1 3 5 3 1) (1 1 1 3 1)
;    (2 3 5 1) (6 1 3 4) (3 2 4) (3 2 2) (6 2 2)
;    (4 1 1 1) (2 1 1 2) (1 1 1 1) (4 2 2) (7)))

;; An example of the nonogram puzzle
;;          3 5 3 3 4 2 3 2 2 2 2 6 4 3 6 7 4 4 7 3
;;              1 1 1 1 1 2 2 2 3 4 2 2 1 2 4 2
;;                5 3 4 1 1 1 2 1 1 2 1 2 2 1
;;                  3 2 1 1 1 1 1   4 4   1
;;                                  3
;;
;;7       
;;10
;;5 4
;;4 9
;;12 2
;;2 7
;;2 5
;;9 3
;;1 4 2
;;1 5
;;2 1
;;1 2
;;2 1 3
;;1 1 5
;;1 2 5
;;1 1 4
;;2 1 1 1
;;1 2 1 1
;;2 1 1 2
;;8 4

;;Remember that if a row or a col don't contain any number you have
;;to put () in this place

;;Change it to run2 if you only want to see the solution.
(time (run *col-lst* *row-lst*))

