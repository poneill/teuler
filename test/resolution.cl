; Begin by importing teuler.
(load #p"../teuler.cl")

;; Here we have test-data for part one, and the output below.  As is
;; evident, resolutions 1 and 5 succeed, and the rest fail.

(defvar test-data 
      '((((p x) (q (f x))) ((~ (p a)) (r y)))
	(((p a) (~ (q x))) ((~ (p b)) (q (f b))))
	(((~ (p a)) (q (f x))) ((p (f y)) (~ (q (g y)))))
	(((q x a b) (p (f x a) (g x b))) ((~ (p y (g y b))) (r y)))
	(((p x (g x) (h b))) ((~ (p (f u a) v u))))))

;; CL-USER> (apply #'resolve (first test-data))
;; (((Q (F A)) (R Y)) ((P X) (Q (F X))) ((~ (P A)) (R Y)) ((SLASH X A)))
;; CL-USER> (apply #'resolve (second test-data))
;; "failure"
;; CL-USER> (apply #'resolve (third test-data))
;; "failure"
;; CL-USER> (apply #'resolve (fourth test-data))
;; "failure"
;; CL-USER> (apply #'resolve (fifth test-data))
;; (NIL ((P X (G X) (H B))) ((~ (P (F U A) V U)))
;;  ((SLASH U (H B)) (SLASH V (G (F (H B) A))) (SLASH X (F (H B) A))))



(defvar kb '(((dog d))   
	    ((owns jack d))
	    ((~ (dog y))  (~ (owns x  y))  (animallover x))
	    ((~ (animallover x))  (~ (animal y))  (~ (kills x y)))
	    ((kills jack tuna)  (kills curiosity tuna))
	    ((cat tuna))
	    ((~ (cat x))  (animal x))))

(defvar goal '((kills curiosity tuna)))

;OUTPUT:
;; CL-USER> (give-proof-for goal kb)

;; ("((CAT TUNA)) was assumed" "((DOG D)) was assumed"
;;  "((KILLS JACK TUNA) (KILLS CURIOSITY TUNA)) was assumed"
;;  "((OWNS JACK D)) was assumed"
;;  "((~ (DOG Y)) (~ (OWNS X Y)) (ANIMALLOVER X)) was assumed"
;;  "((~ (DOG D)) (ANIMALLOVER JACK)) follows from
;;  ((OWNS JACK D)) and ((~ (DOG Y)) (~ (OWNS X Y)) (ANIMALLOVER X))"
;;  "((~ (ANIMALLOVER X)) (~ (ANIMAL Y)) (~ (KILLS X Y))) was assumed"
;;  "((~ (DOG D)) (~ (ANIMAL Y)) (~ (KILLS JACK Y))) follows from
;;  ((~ (DOG D)) (ANIMALLOVER JACK)) and ((~ (ANIMALLOVER X)) (~ (ANIMAL Y))
;;                                        (~ (KILLS X Y)))"
;;  "((KILLS CURIOSITY TUNA) (~ (DOG D)) (~ (ANIMAL TUNA))) follows from
;;  ((KILLS JACK TUNA) (KILLS CURIOSITY TUNA)) and ((~ (DOG D)) (~ (ANIMAL Y))
;;                                                  (~ (KILLS JACK Y)))"
;;  "((~ (CAT X)) (ANIMAL X)) was assumed"
;;  "((KILLS CURIOSITY TUNA) (~ (DOG D)) (~ (CAT TUNA))) follows from
;;  ((KILLS CURIOSITY TUNA) (~ (DOG D)) (~ (ANIMAL TUNA))) and ((~ (CAT X))
;;                                                              (ANIMAL X))"
;;  "((KILLS CURIOSITY TUNA) (~ (CAT TUNA))) follows from
;;  ((DOG D)) and ((KILLS CURIOSITY TUNA) (~ (DOG D)) (~ (CAT TUNA)))"
;;  "((KILLS CURIOSITY TUNA)) follows from
;;  ((CAT TUNA)) and ((KILLS CURIOSITY TUNA) (~ (CAT TUNA)))"
;;  "NIL follows from
;;  ((~ (KILLS CURIOSITY TUNA))) and ((KILLS CURIOSITY TUNA))")

;;  Reading from the bottom up, the contradictory null clause is
;;  presented on the last line, and the theorem prover states that it
;;  was derived from the propositions that Curiousity both did and did
;;  not kill the cat.  Justification for each line is given
;;  recursively until all clauses are grounded in the knowledge base.

; PART III: "I'm my own grandpa"
;we begin with a knowledge base that encodes genealogical relationships;

(defvar wirth-kb '(
		   ;Genealogical rules
		   ((~ (spouse x y)) (wife x y) (husband x y)); defn of marriage
		   ((~ (parent x y)) (father x y) (mother x y)); defn of parent
		   ((~ (child x y)) (parent y x))            ; defn of child
		   ((~ (son x y)) (child x y))                 ; defn of son
		   ((~ (daughter x y)) (child x y))            ; defn of daughter
		   ((~ (spouse x y)) (husband x y) (wife x y))
		   ((~ (step-daughter x y)) (daughter x (f x y)))
		   ((~ (step-daughter x y)) (spouse y (f x y)))
		   ((~ (step-daughter x y)) (~ (parent y x)))  ; defn of step-daughter
		   ((~ (step-son x y)) (son x (f x y)))
		   ((~ (step-son x y)) (spouse y (f x y)))
		   ((~ (step-son x y)) (~ (parent y x)))  ; defn of step-son
		   ((~ (step-child x y)) (child x (g x y)))
		   ((~ (step-child x y)) (spouse y (g x y)))
		   ((~ (step-child x y)) (~ (parent y x)))  ; defn of step-child
		   ((~ (child-in-law x y)) (child (h x y) y))
		   ((~ (child-in-law x y)) (spouse x (h x y)))
		   ((~ (child-in-law x y)) (~ (parent y x)))  ; defn of child-in-law
		   ((~ (step-child x y)) (step-son x y) (step-daugher x y))
		   ((~ (brother x y)) (parent (g x y) x))
		   ((~ (brother x y)) (parent (g x y) y))      ; defn of brother
		   ((~ (brother-in-law x y)) (married y (h x y)))
		   ((~ (brother-in-law x y)) (parent (h x y) y)) ; defn of BIL
		   ((~ (uncle x y)) (parent (i x y) y))
		   ((~ (uncle x y)) (brother x (i x y)))        ;defn of uncle
		   ((~ (gen-parent x y)) (parent x y) (step-child y x) (child-in-law y x))
		   ((~ (gen-grandparent x y)) (gen-parent (i x y) y))
		   ((~ (gen-grandparent x y)) (gen-parent y (i x y)))   ;defn of grandfather
;--------------------------------------------------------------------------------
					;particular facts
		   ((spouse m w)) ;I married the widow
		   ((daughter d w)) ; the widow has a daughter
		   ((father f m)) 
		   ((husband f d)) ; my father married the daughter
		   )
)
(defvar wirth-goal '((gen-grandparent m m)))
;--------------------------------------------------------------------------------

;;This test is unsuccessful so far, due to the size of the
;;knowledge base and the limitations of the theorem prover.  Even
;;after paring down the genealogical knowledge to exclude all
;;relationships that were not strictly necessary to derive the
;;goal-theorem, the theorem was never derived before exhaustion of the
;;heap.  Even after prioritizing constants, even trivial theorems such
;;as the propositions already encoded by the knowledge base were not
;;always found.  The refutation resolution procedure with random
;;clause-picking proved extremely sensitive to initial conditions: if
;;the first few contributions to the knowledge-base were not chosen
;;fortuitously, i.e. productively, the prover ''spun off'' into
;;irrelevant directions, since the probability of picking worthwhile
;;clauses for resolution diminished as the size of the knowledge base increased.
