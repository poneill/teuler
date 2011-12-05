
(defun literal-identification (clause1 clause2)
  "return a list of opposite literals between clause1, clause2"
  (let ((arg-pairs (cross clause1 clause2)))
    (remove-if-not (lambda (pair) (apply #'opposite? pair)) arg-pairs)))

(defun opposite? (p q)
  "determine whether p and q are opposite literals"
  (cond ((and (negated? p) (not (negated? q))) (eq (caadr p) (car q)))
	((and (not (negated? p)) (negated? q)) (eq (car p) (caadr q)))
	(t nil)))

(defun resolve (c1 c2)
  (let* ((opp-pair (car (literal-identification c1 c2))))
    (if opp-pair
	(let* ((opp1 (first opp-pair))
	       (opp2 (second opp-pair))
	       (mgu (unify (arg-list opp1) (arg-list opp2))))
	  (if (eq mgu "failure")
	      "failure"
	      (sub (append (remove opp1 c1) (remove opp2 c2)) mgu)))
	  "failure")))

(defun test-resolve (c1 c2)
  (let* ((opp-pair (car (literal-identification c1 c2))))
    (if opp-pair
	(let* ((opp1 (first opp-pair))
	       (opp2 (second opp-pair))
	       (mgu (unify (arg-list opp1) (arg-list opp2))))
	  (if (eq mgu "failure")
	      "failure"
	      (list (sub (append (remove opp1 c1) (remove opp2 c2)) mgu) c1 c2 mgu)))
	nil)))

(defun arg-list (p)
  (if (negated? p)
      (cdadr p)
      (rest p)))

(defun negated? (p)
  (if (listp p)
      (eq (car p) '~)
      nil))

(defun cross (xs ys)
	   (apply #'append 
		  (mapcar (lambda (x) 
			    (mapcar (lambda (y) (list x y)) 
				    ys)) 
			  xs)))

(defun same-function? (p q)
  (or (eq (car p) (car q))
      (and (negated? p) (negated? q) 
	   (same-function? (cdr p) (cdr q)))))

(defun unify (p q &optional (theta nil))
  (if (null p) 
      theta
      (let* ((r (first p))
	     (s (first q)))
	(cond ((equal r s) (unify (rest p) (rest q) theta))
	      (t (let ((temp
			(cond ((variable? r) (unify-var r s))
			      ((variable? s)  (unify-var s r))
			      ((same-function? p q)
			       (unify-var (arg-list p) (arg-list q)))
			      (t "failure"))))
		   (if (eq temp "failure")
		       "failure"
		       (let ((theta-prime (append temp (sub theta temp))))
			 (unify (sub (rest p) temp) 
				(sub (rest q) temp) 
				theta-prime)))))))))
(defun variable? (v)
  (member v '(u v x y z)))

(defun unify-var (x y)
  (if (appears-in? x y)
      "failure"
      `((slash ,x ,y))))

(defun appears-in? (x ys)
  (if (atom ys)
      (eq x ys)
      (some (lambda (y) (funcall #'appears-in? x y)) ys)))

(defun sub (theta temp)
  (if (null temp)
      theta
      (let ((slashpair (car temp))
	    (slashpairs (cdr temp)))
	(sub (subst (substitutor slashpair) 
		    (substituendum slashpair) 
		    theta) slashpairs))))

(defun substituendum (slashpair)
  (second slashpair))

(defun substitutor (slashpair)
  (third slashpair))

(defun fold (f xs)
  (if (= (length xs) 1)
      (car xs)
      (fold f (cons (funcall f (first xs) (second xs)) (cddr xs)))))


;; Part II

(defun negate (p)
  (cancel-negation (append '(~) (list p))))

(defun negate-clause (p)
  (mapcar #'negate p))

(defun prove (kb goal)
  (if (elem goal kb) 
      (progn 
	(print "found in kb:")
	(print goal))
      (let* ((pq (derive-contradiction (strict-union kb (list (negate-clause goal)))))
	     (p (first pq))
	     (q (second pq)))
	(prove kb (negate-clause p))
	(prove kb (negate-clause q)))))

(defun strict-union (xs ys)
  (union xs ys :test #'equal))

(defun elem (xs ys)
  (member xs ys :test #'equal))

(defun derive-contradiction (kb)
  (let* ((pq (pick-two kb))
	 (result (apply #'resolve pq)))
    (cond ((equal result "failure") (derive-contradiction kb)) 
	  ((null result) pq) ;return the clauses giving the final contradiction 
	  (t (derive-contradiction (strict-union kb (list result)))))))

(defun resolve-all (kb)
  "generate all first-level resolvents from kb"
  (remove-if (lambda (x) (equal x "failure"))
	     (mapcar (lambda (pair) (apply #'resolve pair)) 
		     (cross kb kb))))

(defvar *hash* (make-hash-table :test #'equal))

(defun proof-wrapper (kb goal)
  (let* ((*hash* (make-hash-table :test #'equal)))
    (hash-derive-contradiction (cons (negate-clause goal) kb))))

(defun give-proof-for (goal kb)
  (pprint (interpret-hash kb (proof-wrapper kb goal))))

(defun naive-prove (kb goal)
  (let* ((pq (pick-two kb))
	 (result (apply #'resolve pq)))
    (cond ((equal result goal) "proved!")
	  ((equal result "failure") (naive-prove kb goal))
	  (t (naive-prove (strict-union kb (list result)) goal)))))

;(defparameter *hash* (make-hash-table :test #'equal))

(defun hash-prove (kb goal)
  (let* ((pq (pick-two kb))
	 (result (apply #'resolve pq))
	 (worthwhile (and (not (equal result "failure"))
			  (not (gethash result *hash*)))))
    (if worthwhile
	(progn (setf (gethash result *hash*) pq)
	       (if (equal result goal)
		   (print "proved!")
		   (hash-prove kb goal)))
	(hash-prove kb goal))))
    
(defun hash-derive-contradiction (kb &optional (tried nil))
  (if (= (length tried) (expt (length kb) 2))
      "exhausted knowledge base"
      (let* ((pq (pick-two kb tried))
	     (result (apply #'resolve pq))
	     (tried-prime (cons pq tried)))
	(cond ((equal result "failure") (hash-derive-contradiction kb tried-prime))
	      ((gethash result *hash*) (hash-derive-contradiction kb tried-prime))
	      ((null result) (progn
			       (setf (gethash result *hash*) pq)
			       ;pq)) ;return the clauses giving the final contradiction
			       *hash*))
	      (t (progn
		   (setf (gethash result *hash*) pq)
		   (hash-derive-contradiction (strict-union kb (list result)) tried-prime)))))))

(defun interpret-hash (kb hash &optional (goal nil) (interpreted nil) (proof-string nil))
  (progn
    (cond ((elem goal kb) (cons (format nil "~S was assumed" goal) (id proof-string)))
	  ((elem goal interpreted) nil)
	  (t (let* ((resolvents (gethash goal hash))
		    (p (first resolvents))
		    (q (second resolvents))
		    (interpreted-prime (append interpreted (list goal)))
		    (new-string (list (format nil "~S follows from~% ~S and ~S" goal p q))))
	       (remove-duplicates (append (interpret-hash kb hash p interpreted-prime new-string)
					  (interpret-hash kb hash q interpreted-prime new-string)
					  proof-string) 
				  :test #'equal))))))

(defun id (x) x)

(defun tree-elem (x ys)
  (if (atom ys)
      (equal x ys)
      (not (null (remove nil (mapcar (lambda (y) (tree-elem x y)) ys))))))

(defun pick-two (kb &optional (tried nil) (prioritize-constants nil))
  (let* ((r1 (random-choice kb))
	 (r2 (remove r1 (random-choice kb)))
	 (pq (list r1 r2)))
    (if (and (not (elem pq tried))
	     (or (not prioritize-constants)
		 (tree-elem 'm pq)
		 (tree-elem 'w pq)
		 (tree-elem 'd pq)
		 (tree-elem 'f pq)))
	pq
	(pick-two kb tried))))

(defun random-choice (xs)
  (nth (random (length xs)) xs))

(defun print-hash-entry (key value) ;taken from from cl cookbook
    (format t "The value associated with the key ~S is ~S~%" key value))

(defun readhash (hash)
  (maphash #'print-hash-entry hash))

(defun print-proof (proof)
  (mapcar #'print proof))

(defun skolem-constant ()
  (gensym))

(defun skolem-function (universal-quants)
  (cons (gensym) universal-quants))

(defun conjoin (c1 c2)
  (list 'and c1 c2))

(defun disjoin (c1 c2)
  (list 'or c1 c2))

(defun imply (c1 c2)
  (list '=> c1 c2))

(defun biconditional? (formula)
  (and (listp formula)
       (equal (first formula) '<=>)))

(defun conditional? (formula)
  (and (listp formula)
  (equal (first formula) '=>)))

(defun conjunctive? (formula)
  (and (listp formula)
       (equal (first formula) 'and)))

(defun disjunctive? (formula)
  (and (listp formula)
       (equal (first formula) 'or)))

(defun conjunction-free? (formula)
  (if (atom formula)
      (not (equal formula 'and))
      (every #'conjunction-free? formula)))

(defun disjunction-of-literals? (formula)
  (and (disjunctive? formula)
       (conjunction-free? formula)))

(defun junction? (sym)
  (or (equal sym 'or) (equal sym 'and)))

(defun demorganable? (formula)
  (and (negated? formula) (junction? (first (second formula)))))

(defun existential? (formula)
  (equal (first formula) 'there-exists))

(defun universal? (formula)
  (equal (first formula) 'forall))

(defun cnf? (formula)
  (and (conjunctive? formula)
       (every #'conjunction-free? (rest formula))))

(defun convert (formula &optional (universal-quants nil))
  (defun convert-prime (form) (convert form universal-quants));erryday I be symbol-shuntin
  (cond ((biconditional? formula) 
	 (let ((c1 (second formula))
	       (c2 (third formula)))
	   (convert-prime (conjoin (imply c1 c2)
				   (imply c2 c1)))))
	((conditional? formula)  (convert-prime (disjoin (convert-prime 
							  (negate (second formula))) 
							 (convert-prime 
							  (third formula)))))
	((demorganable? formula) (convert-prime (distribute formula)))
	((existential? formula)
	 (let ((variable (second formula))
	       (body (third formula)))
	   (if universal-quants
	       (subst (skolem-function universal-quants) variable body)
	       (subst (skolem-constant) variable body))))
	((universal? formula) 
	 (let ((variable (second formula))
	       (body (third formula)))
	   (convert body (cons variable universal-quants))))
	(t formula)))

(defun distribute (formula)
  (cond ((atom formula) formula)
	((and (disjunctive? formula) (conjunctive? (second formula)))
	 (let ((a (distribute (second (second formula))))
	       (b (distribute (third (second formula))))
	       (c (distribute (third formula))))
	   (conjoin (disjoin a c) (disjoin b c))))
	((and (disjunctive? formula) (conjunctive? (third formula)))
	 (let ((a (distribute (second formula)))
	       (b (distribute (second (third formula))))
	       (c (distribute (third (third formula)))))
	   (conjoin (disjoin a c) (disjoin b c))))
	(t (mapcar #'distribute formula))))
	 
(defun fixpoint (f x)
  (let ((z (funcall f x)))
    (if (equal z x)
	z
	(fixpoint f z))))

(defun flip-connective (sym)
  (if (equal sym 'or)
      'and
      'or))

(defun cancel-negation (formula)
  (if (and (listp formula)
	   (listp (second formula))
	   (equal (first formula) '~)
	   (equal (first (second formula)) '~))
      (second (second formula))
      formula))

(defun drop-ands (formula)
  (cond ((conjunctive? formula) (mapcar #'drop-ands (rest formula)))
	(t formula)))

(defun drop-ors (formula)
  (cond ((disjunctive? formula) (mapcar (lambda (x) (list x)) (rest formula)))
	(t formula)))