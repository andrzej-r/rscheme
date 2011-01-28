;;  Copyright (c) Andrzej Radecki. All rights reserved.
;;  The use and distribution terms for this software are covered by the
;;  Common Public License 1.0 (http://opensource.org/licenses/cpl.php)
;;  which can be found in the file CPL.txt at the root of this distribution.
;;  By using this software in any fashion, you are agreeing to be bound by
;;  the terms of this license.
;;  You must not remove this notice, or any other, from this software.
;;
;;  File: rscheme.clj
;;
;;  rscheme.clj contains an implementation of a reader and an evaluator
;;  of a simple, scheme-like language. It can be used as a sand-box
;;  (an isolated and restricted execution environment) for interpreting
;;  scripts that if executed directly by clojure could pose a security
;;  risk to the system.
;;
;;  Note that this software was neither developed for conformance with the R5RS
;;  standard nor for the execution efficiency.
;;
;;  Functions:
;;    'eval' - scheme evaluator (stub)
;;    'read' - scheme reader
;;    'repl' - Read-Eval-Print-Loop function of the scheme interpreter
;;
;; (gmail) nrdwrdck
;; 09 May 2008
;;

(in-ns 'rscheme)
(clojure/refer 'clojure :exclude '(eval read))

(def #^{:private true} stack-depth 100)

(def #^{:private true} trace 0)

(def #^{:private true} eval)

(def #^{:private true} print-exp)

(defn- make-number [n]
  {:type :number :val n})

(defn- make-bool [n]
  {:type :bool :val n})

(defn- make-true
  {:type :bool :val true})

(defn- make-false
  {:type :bool :val false})

(defn- make-list [l]
  {:type :list :val l})

(defn- make-nil []
  (make-list nil))

(defn- is-symbol? [t]
  (= (:type t) :symbol))

(defn- is-list? [t]
  (= (:type t) :list))

(defn- is-nil? [l]
  (and (= (:type l) :list) (nil? (:val l))))

(defn- with-env [val env]
  (assoc val :env env))

(defn- val-op
  "Performs an operation op on field :val of a map mp
   and return the modified map"
  [mp op]
  (let [inner (:val mp)]
    (assoc mp :val (op inner))))

(defn- val-conj
  [mp val]
  (val-op mp (fn [inner] (conj inner val))))

(defn- val-first [mp]
  (val-op mp first))

(defn- val-rest [mp]
  (val-op mp rest))

(defn- val-frest [mp]
  (val-op mp frest))

(defn- val-rrest [mp]
  (val-op mp rrest))

(defn- prim_add
  [& xs]
  (make-number (apply + (map :val xs))))

(defn- prim_sub
  [& xs]
  (make-number (apply - (map :val xs))))

(defn- prim_mul
  [& xs]
  (make-number (apply * (map :val xs))))

(defn- prim_div
  [& xs]
  (make-number (apply / (map :val xs))))

(defn- prim_gt
  [& xs]
  (make-bool (apply > (map :val xs))))

(defn- prim_lt
  [& xs]
  (make-bool (apply < (map :val xs))))

(defn- prim_eq
  [& xs]
  (make-bool (apply = (map :val xs))))

(defn- prim_display-helper
  [int? first? & xs]
  ;;(println first? xs)
  (if (nil? xs)
    (make-nil)
    (do (if (not first?)
      (print " "))
    (print-exp int? (first xs))
    (recur int? false (rest xs)))))

(defn- prim_display
  [& xs]
  (apply prim_display-helper false true xs))

(defn- prim_write
  [& xs]
  (apply prim_display-helper true true xs))

(defn- frrest  [l] (-> l rrest first))
(defn- frrrest [l] (-> l rrest rest first))

(defn- pos-string [ann]
  (str (:fname ann) ":" (:line ann) ":" (:col ann)))

(defn- indent
  "Displays lvl consequtive [char] characters"
  [char lvl]
  (when (pos? lvl)
    (do (print char) (recur char (dec lvl)))))

(defn- print-bool
  [val]
  (if val
    (print "#t")
    (print "#f")))

(defn- print-number
  [val]
  (print val))

(defn- print-char
  [int? val]
  (if int?
    (pr val)
    (print val)))

(defn- print-string
  [int? val]
  (if int?
    (pr val)
    (print val)))

(defn- print-symbol
  [val]
  (print (name val)))

(defn- print-list
  ([val]
     (print-list val true))
  ([val first?]
     (if first? (print "("))
     (if (nil? val)
       (print ")")
       (do (if (not first?)
         (print " "))
       (print-exp true (first val))
       (recur (rest val) false)))))

(defn- print-exp
  [int? exp]
  (when (map? exp)
    (let [type (:type exp) val (:val exp)]
      ;;(println type val)
      (cond
       (= type :bool)        (print-bool (:val exp))
       (= type :number)        (print-number (:val exp))
       (= type :char)        (print-char int? (:val exp))
       (= type :string)        (print-string int? (:val exp))
       (= type :symbol)        (print-symbol (:val exp))
       (= type :list)        (print-list (:val exp))))))

(defn- extend-environment
  [env arg-list param-list]
  (cond (and (nil? arg-list) (nil? param-list))
    env
    (or (= (count arg-list) 0) (= (count param-list) 0))
    nil
    :else
    (recur (assoc env (:val (first arg-list)) (first param-list))
           (rest arg-list) (rest param-list))))

(defn- extend-env
  [env arg-list param-list def-ok? tail?]
  (extend-environment
   {:parent env :level (+ 1 (:level env)) :tail? tail? :def-ok? def-ok?}
   arg-list param-list))

(defn- make-env [env def-ok? tail?]
  (extend-env env nil nil def-ok? tail?))

(defn- eval-sequence
  "Eval a list of forms. Tail recursive.
   \"define's\" are only allowed at the beginning of the list."
  ([exps env]
     (eval-sequence exps env (with-env (make-nil) env) true))
  ([exps env res def-ok]
     (if (nil? exps)
       res
       (let [res (eval (first exps)
               (assoc env
             :def-ok? def-ok
             :tail? (nil? (rest exps))))
         env (:env res)
         def-ok (:definition res)]
     (recur (rest exps) env res def-ok)))))

(defn- eval-sequence-top
  "Eval a top-level list of forms.
   \"define's\" are always allowed.
   Not tail recursive (is it necessary(?))"
  ([exps env]
     (eval-sequence-top exps env (with-env (make-nil) env)))
  ([exps env res]
     (if (nil? exps)
       res
       (let [res (eval (first exps) env)
         env (:env res)]
     (recur (rest exps) env res)))))

(defn- eval-symbol
  ([exp env]
     (let [name (:val exp)]
       (eval-symbol exp env env name)))
  ([exp env-orig env var]
     (if (contains? env var)
       (with-env (get env var) env-orig)
       (if (nil? (:parent env))
     (do (println
          (str "Unbound variable " (:val exp) ", "
           (pos-string (:start exp))))
         (with-env (make-nil) env-orig))
     (recur exp env-orig (:parent env) var)))))

(defn- eval-quote
  [exp env]
  (when (> (count (:val exp)) 2)
    (let [ann (:start exp)]
      (println
       (str "Unused arguments to \"quote\", "
        (pos-string ann)))))
  (with-env (frest (:val exp)) env))

(defn- eval-assign
  [exp env]
  )

(defn- eval-if
  "add error checking"
  [exp env]
  (let [vec (:val exp) cond (frest vec) pred (frrest vec) alt (frrrest vec)]
    ;;(let [c (eval cond (make-env env false true))]
    (let [c (eval cond (assoc env :def-ok? false :tail? true))]
      (if (:val c)
    ;;(eval pred (make-env env false true))
    (eval pred (assoc env :def-ok? false :tail? true))
    (if (nil? alt)
      (with-env (make-nil) env)
      ;;(eval alt (make-env env false true)))))))
      (eval alt (assoc env :def-ok false :tail? true)))))))

(defn- eval-cond
  [exp env]
  )

(defn- parse-formals-list
  ([lst exp]
     (parse-formals-list lst exp (list) nil))
  ([lst exp res res2]
     (if (nil? lst)
       {:arg-list (reverse res) :arg-rest (reverse res2)}
       (if (is-symbol? (first lst))
     (recur (rest lst) exp (cons (first lst) res) res2)
     (println
      (str "Invalid symbol in the argument list "
           (pos-string (:start exp))))))))

(defn- parse-formals
  ([var exp env]
  (cond (= (:type var) :symbol)
    {:arg-rest var :arg-list nil}
    (= (:type var) :list)
    (parse-formals-list (:val var) exp)
    :else
    (println
     (str "Invalid argument list "
          (pos-string (:start exp)))))))

(defn- eval-lambda
  [exp env]
  (let [vec (:val exp) var (frest vec)
    body (rrest vec)]
    ;;body (subvec vec 2)]
    (if (or (nil? var) (nil? body))
      (do (println
       (str
        "Not enough arguments to \"lambda\" "
        (pos-string (:start exp))))
      (with-env (make-nil) env))
      (let [formals (parse-formals var exp env)
        arg-list (:arg-list formals)
        arg-rest (:arg-rest formals)]
    (if (nil? formals)
      (with-env (make-nil) env)
      (with-env {:body body :arg-list arg-list
             :arg-rest arg-rest :type :fun
             :start (:start exp) :end (:end exp)}
            env))))))

(defn- eval-define
  [exp env]
  (let [vec (:val exp) var (frest vec) val-exp (frrest vec)]
    (cond
     ;;value
     (and (= (:type var) :symbol)
      (not (nil? val-exp)))
     (let [res (eval val-exp (make-env env false true))
       val (dissoc res :env)
       env (:parent (:env res))]
       (with-env res (assoc env (:val var) val)))
     ;;procedure
     (and (= (:type var) :list)
      (= (:type (first (:val var))) :symbol)
      (not (nil? val-exp)))
     (let [sym (first (:val var))
       ;;args (subvec (:val var) 1)
       ;;body (subvec vec 2)
       args (rest (:val var))
       body (rrest vec)
       formals (parse-formals-list args var)
       arg-list (:arg-list formals)
       arg-rest (:arg-rest formals)
       res {:body body :arg-list arg-list
        :arg-rest arg-rest :type :fun
        :start (:start exp) :end (:end exp)}]
       (if (nil? formals)
     (with-env (make-nil) env)
     (with-env res (assoc env (:symbol sym) res))))
     ;;unknown
     :else
     (let [ann (:start var)]
       (println
    (str "Invalid format of \"define\" form "
         (pos-string ann)))
       (with-env (make-nil) env)))))

(defn- eval-begin
  [exp env]
  )

(defn- eval-and
  [exp env]
  )

(defn- eval-or
  [exp env]
  )

(defn- eval-arguments
  ([exps env]
     (eval-arguments exps env (list)))
  ([exps env lst]
     (if (nil? exps)
       (reverse lst)
       ;;(let [res (eval (first exps) (make-env env false false))
       (let [res (eval (first exps) (assoc env :def-ok? false :tail? false))
         val (dissoc res :env)]
     (recur (rest exps) env (cons val lst))))))

(defn- eval-primitive
  [op exp env]
  ;;{:val (apply (get primitives (:val (first exp))) '(5 6))
  (let [res (apply (:val op)
           (eval-arguments
            (rest (:val exp))
            env))]
    (when (> trace 1)
      (indent "+" (:level env))
      (print " ")
      (print-exp true res)
      (print "\t")
      (print-exp true exp)(newline))
    (with-env res env)))

(defn- eval-procedure
  [op exp env]
  (let [params (eval-arguments (rest (:val exp)) env)
    nenv
    (if (:tail? env)
      (extend-environment env (:arg-list op) params)
      (extend-environment
       {:parent env :level (+ 1 (:level env)) :tail? false}
       (:arg-list op) params))]
    (cond (nil? nenv)
      (do (println
           (str
        "Procedure applied to wrong number of arguments. "
        "Expected " (count (:arg-list op))
        ", given " (count params) ". " (pos-string (:start exp))))
          (with-env (make-nil) env))
      (> (:level env) stack-depth)
      (do (println
           (str
        "Stack overflow, " (pos-string (:start exp))))
          (with-env (make-nil) env))
      :else
      (let [res (eval-sequence (:body op) nenv)]
        (if (:tail? env)
          res
          (do (with-env (dissoc res :env) (:parent (:env res)))))))))

(defn- eval-application
  [exp env]
  ;;(let [op (eval (first (:val exp)) (make-env env false false))]
  (let [op (eval (first (:val exp))
         (assoc env :def-ok? false :tail? false))]
    (cond (= (:type op) :primitive-fun)
      (eval-primitive op exp env)
      (= (:type op) :fun)
      (eval-procedure op exp env)
      ;;(is-nil? op)
      ;;(with-env (make-nil) env)
      :else
      (do (println
           (str "First element of the form is not a procedure, "
            (pos-string (:start exp))))
          (with-env (make-nil) env)))))

;;----

(defmulti eval-form
  (fn [exp env]
      (when (> trace 0)
    (indent "-" (:level env))
    (print " ")
    (print-exp true exp)(newline))
      (:val (first (:val exp)))))

(defmethod eval-form 'quote
  [exp env]
  (eval-quote exp env))

(defmethod eval-form 'set!
  [exp env]
  (eval-assign exp env))

(defmethod eval-form 'define
  [exp env]
  (if (:def-ok? env)
    (eval-define exp env)
    (do (println
     (println
      (str "Definition is not allowed in this context, "
           (pos-string (:start exp)))))
    (with-env (make-nil) env))))

(defmethod eval-form 'if
  [exp env]
  (eval-if exp env))

(defmethod eval-form 'cond
  [exp env]
  (eval-cond exp env))

(defmethod eval-form 'lambda
  [exp env]
  (eval-lambda exp env))

(defmethod eval-form 'begin
  [exp env]
  (eval-begin exp env))

(defmethod eval-form 'and
  [exp env]
  (eval-and exp env))

(defmethod eval-form 'or
  [exp env]
  (eval-or exp env))

(defmethod eval-form :default
  [exp env]
  (eval-application exp env))

;;-----

(defmulti eval (fn [exp env] (:type exp)))

(defmethod eval :bool
  [exp env]
  (with-env exp env))

(defmethod eval :number
  [exp env]
  (with-env exp env))

(defmethod eval :char
  [exp env]
  (with-env exp env))

(defmethod eval :string
  [exp env]
  (with-env exp env))

(defmethod eval :symbol
  [exp env]
  (when (> trace 2)
    (indent "-" (:level env))
    (print " ")
    (print-exp true exp)(newline))
  (let [res (eval-symbol exp env)]
    (when (> trace 2)
      (indent "+" (:level env))
      (print " ")
      (print-exp true res)
      (print "\t")
      (print-exp true exp)(newline))
    res))

(defmethod eval :list
  [exp env]
  (eval-form exp env))

(defmethod eval :default
  [exp env]
  (println
   (str "Unrecognised expression "
    (pos-string (:start exp))))
  (with-env (make-nil) env))

(defn- prompt-for-input
  "Displays an input prompt"
  []
  (println)
  (println "Scheme: ")
  (flush))

(defn- output-prompt
  "Displays a result prompt"
  []
  (newline)
  (println "Result:"))

(defn- pprint
  "A simple \"pretty print\" function suitable for debugging syntax trees
  (as returned by read function)"
  ([val]
     (pprint val 0))
  ([val lvl]
     (indent " " lvl)
     (if (and (= (:type val) :list) (not (nil? (:val val))))
       (do
     (println "(")
     (doseq elem (:val val) (pprint elem (+ lvl 2)))
     (indent " " lvl)
     (println ")"))
       (prn val))))

(defn- next-pos
  "Returns a structure containing line, column and character number of the
  character to be read.
  pos - line, column and character number of the current character
  ch - current character"
  [pos ch]
  (let [ch (char ch) line (:line pos) col (:col pos) cnt (+ (:cnt pos) 1)]
    (if (= ch \newline)
      (assoc pos :line (+ line 1) :col 1 :cnt cnt)
      (assoc pos :line line :col (+ col 1) :cnt cnt))))

(defn- char-seq-helper
  [stream close? pos]
     (let [ch (. stream (read))]
       (if (== ch -1)
     (when close?
       (. stream (close)))
     ;; (lazy-cons (. Character (toString (char ch)))
     ;; (char-seq stream close?))))))
     (lazy-cons (assoc pos :ch (char ch))
       (char-seq-helper stream close? (next-pos pos ch))))))

(defn char-seq
  "Reads an input stream (*in* if called without arguments) and returns
  a lazy sequence of characters in this stream"
  ([]
     (char-seq *in*))
  ([stream]
     (char-seq stream "STDIN" false))
  ([stream fname close?]
     (char-seq-helper stream close? {:line 1, :col 1, :cnt 1, :fname fname})))

(defn char-seq-from-file
  "Reads an input file f and returns a lazy sequence of characters
  included this file"
  [#^String f]
  ;; (with-open r (new java.io.FileReader f)
  (let [r (new java.io.FileReader f)]
    (char-seq r f true)))

(defn- whitespace?
  [ch]
  (. Character (isWhitespace ch)))

(defn- digit?
  [ch]
  (. Character (isDigit ch )))

(defn- tappend
  "Appends characters (chars) to the :txt field of the token structure"
  [token & chars]
  (assoc token :txt (reduce str (:txt token) chars)))

(defn- delimiter?
  "Is character (ch) a delimiter?"
  [ch]
  (or (whitespace? ch) (= ch \() (= ch \)) (= ch \;)
      (= ch \") (= ch \') (= ch \`) (= ch \,)))

(defn- parse-unicode
  ([cseq]
     (parse-unicode cseq 4 0))
  ([cseq cnt val]
     (if (= cnt 0)
       val
       (let [ch (:ch (first cseq))
         digit (. Character (digit ch 16))]
     (if (= digit -1)
       nil
       (recur (rest cseq) (- cnt 1) (+ (* val 16) digit)))))))

(defn- escape-char
  [cseq]
  (let [ch (:ch (frest cseq))]
    (cond (= ch \n) [\newline (rrest cseq)]
      (= ch \t) [\tab (rrest cseq)]
      (= ch \r) [(char 13) (rrest cseq)]
      (= ch \b) [\backspace (rrest cseq)]
      (= ch \f) [\formfeed (rrest cseq)]
      (= ch \\) [\\ (rrest cseq)]
      (= ch \') [\' (rrest cseq)]
      (= ch \") [\" (rrest cseq)]
      (= ch \u) (let [val (parse-unicode (rrest cseq))]
              (if (not (nil? val))
            [(char val) (rrest (rrest (rrest cseq)))]
            [nil (rrest cseq)]))
      :else [nil (rrest cseq)])))

(defn token-seq
  "Consumes a lazy sequence of characters (as returned by char-seq)
  and produces a lazy sequence of tokens.
  If called without arguments it attempts to read characters from
  the *in* stream"
  ([]
     (token-seq (char-seq *in*)))
  ([cseq]
     (token-seq cseq {:type :whitespace}))
  ([cseq token]
     (let [ch (:ch (first cseq)) ann (dissoc (first cseq) :ch)
       type (:type token) text (:txt token)]
       ;; (println ch)
       (cond
    ;; end of stream
    (nil? ch) nil
    ;; comments
    (= type :comment)
    (if (= ch \newline)
      (recur (rest cseq) (assoc token :type :whitespace))
      (recur (rest cseq) token))
    ;; whitespaces (or borders of tokens)
    (= type :whitespace)
    (cond (whitespace? ch) (recur (rest cseq) token)
          (= ch \;) (recur (rest cseq) (assoc token :type :comment))
          (= ch \") (recur (rest cseq)
                   (assoc token :type :string :start ann))
          (or (= ch \-) (= ch \+))
          (recur (rest cseq)
             (assoc (tappend token ch) :type :sign :start ann))
          (digit? ch) (recur (rest cseq)
                 (assoc (tappend token ch)
                   :type :begin-number :start ann))
          (= ch \#) (recur (rest cseq)
                   (assoc (tappend token ch)
                 :type :hash :start ann))
          (= ch \\) (recur cseq
                   (assoc (tappend token ch)
                 :type :char :start ann))
          (= ch \') (lazy-cons
                {:type :symbol :txt (str ch)
                 :val (symbol "quote") :expand true
                 :start ann :end ann}
              (token-seq (rest cseq)))
          (= ch \`) (lazy-cons
                {:type :symbol :txt (str ch)
                 :val (symbol "quasiquote") :expand true
                 :start ann :end ann}
              (token-seq (rest cseq)))
          (= ch \,) (lazy-cons
                {:type :symbol :txt (str ch)
                 :val (symbol "unquote") :expand true
                 :start ann :end ann}
              (token-seq (rest cseq)))
          (= ch \() (lazy-cons
                {:type :lparen :txt (str ch)
                 :start ann :end ann}
              (token-seq (rest cseq)))
          (= ch \)) (lazy-cons
                {:type :rparen :txt (str ch)
                 :start ann :end ann}
              (token-seq (rest cseq)))
          :else (recur (rest cseq)
               (assoc (tappend token ch) :type :symbol
                  :start ann)))
    ;; strings
    (= type :string)
    (cond (= ch \\) (let [res (escape-char cseq)
                  ch (first res)
                  ncseq (second res)]
              (recur ncseq (tappend token ch)))
          (= ch \") (lazy-cons
                (assoc token :val (:txt token) :end ann)
              (token-seq (rest cseq)))
          :else (recur (rest cseq) (tappend token ch)))
    ;; characters
    (= type :char)
    (let [res (escape-char cseq)
          ch2 (first res)
          ncseq (second res)]
      (if (nil? ch2)
        ;;(recur cseq (assoc token :type :unknown))
        (let [ch (:ch (frest cseq))
          ann (dissoc (frest cseq) :ch)]
          (lazy-cons (assoc (tappend token ch)
               :val ch :end ann)
        (token-seq (rrest cseq))))
        (let [ann (dissoc (first ncseq) :ch)]
          (lazy-cons (assoc (tappend token ch2)
               :val ch2 :end ann :ch)
        (token-seq ncseq)))))
    ;; boolean literals
    (= type :hash)
    (cond (or (= ch \t) (= ch \T))
          (lazy-cons
          (assoc (tappend token ch)
            :type :bool :val true :end ann)
        (token-seq (rest cseq)))
          (or (= ch \f) (= ch \F))
          (lazy-cons
          (assoc (tappend token ch)
            :type :bool :val false :end ann)
        (token-seq (rest cseq)))
          :else (recur cseq (assoc token :type :symbol)))
    ;; numbers
    ;; take first digit after sign
    (= type :sign)
    (cond (digit? ch) (recur (rest cseq)
                 (assoc (tappend token ch)
                   :type :begin-number))
          :else (recur cseq (assoc token :type :symbol)))
    ;; take remaining digits of the number and detect the format
    (= type :begin-number)
    (cond (digit? ch) (recur (rest cseq) (tappend token ch))
          (= ch \.) (recur (rest cseq)
                   (assoc (tappend token ch)
                 :type :begin-decimal))
          (= ch \/) (recur (rest cseq)
                   (assoc (tappend token ch)
                 :type :begin-quotient))
          (or (= ch \e) (= ch \E)) (recur
                    (rest cseq)
                    (assoc (tappend token ch)
                      :type :begin-exponent))
          (delimiter? ch)
          (lazy-cons
          (assoc token
            :type :number :val (new BigInteger text) :end ann)
        (token-seq cseq))
          :else (recur (rest cseq)
               (assoc (tappend token ch)
                 :type :unknown :error :numformat)))
    ;; take at least one digit of the decimal part
    (= type :begin-decimal)
    (cond (digit? ch) (recur (rest cseq)
                 (assoc (tappend token ch)
                   :type :decimal))
          :else (recur cseq
               (assoc token :type :unknown :error :numformat)))
    ;; collect remaining digits of the decimal part
    (= type :decimal)
    (cond (digit? ch) (recur (rest cseq) (tappend token ch))
          (or (= ch \e) (= ch \E))
          (recur (rest cseq)
             (assoc (tappend token ch) :type :begin-exponent))
          (or (= ch \m) (= ch \M))
          (recur (rest cseq) (assoc token :type :big-decimal))
          (delimiter? ch)
          (lazy-cons
          (assoc token
            :type :number :val (new Double text) :end ann)
        (token-seq cseq))
          :else (recur (rest cseq)
               (assoc (tappend token ch)
                 :type :unknown :error :numformat)))
    ;; make a "big decimal" value
    (= type :big-decimal)
    (cond
     (delimiter? ch)
     (lazy-cons
         (assoc (tappend token \M) :type :number
            :val (new BigDecimal text) :end ann)
       (token-seq cseq))
     :else (recur (rest cseq)
              (assoc (tappend token ch)
            :type :unknown :error :numformat)))
    ;; at least one digit in quotient
    (= type :begin-quotient)
    (cond (digit? ch) (recur (rest cseq)
                 (assoc (tappend token ch)
                   :type :quotient))
          :else (recur cseq (assoc token
                  :type :unknown :error :numformat)))
    ;; rest of the quotient
    (= type :quotient)
    (cond (digit? ch) (recur (rest cseq) (tappend token ch))
          (delimiter? ch)
          (let [[n d] (split-with (fn [c] (not (= c \/))) text)]
        (lazy-cons
            (assoc token
              :type :number
              :val
              (. clojure.lang.Numbers
              (divide (new BigInteger (apply str n))
                  (new BigInteger (apply str (rest d)))))
              :end ann)
          (token-seq cseq)))
          :else (recur
             (rest cseq) (assoc (tappend token ch)
                   :type :unknown :error :numformat)))
    ;; take first exponent digit or exponent sign
    (= type :begin-exponent)
    (cond (digit? ch) (recur
               (rest cseq)
               (assoc (tappend token ch) :type :exponent))
          (or (= ch \-) (= ch \+)) (recur
                    (rest cseq)
                    (assoc (tappend token ch)
                      :type :begin-exponent-digits))
          :else (recur cseq (assoc token
                  :type :unknown :error :numformat)))
    ;; at least one digit in the exponent
    (= type :begin-exponent-digits)
    (cond (digit? ch) (recur (rest cseq) (assoc (tappend token ch)
                           :type :exponent))
          :else (recur cseq (assoc token
                  :type :unknown :error :numformat)))
    ;; collect digits in the exponent
    (= type :exponent)
    (cond (digit? ch) (recur (rest cseq) (tappend token ch))
          (delimiter? ch)
          (lazy-cons (assoc token
               :type :number :val (new Double text) :end ann)
        (token-seq cseq))
          :else (recur (rest cseq)
               (assoc (tappend token ch)
                 :type :unknown :error :numformat)))
    ;; symbols
    (= type :symbol)
    (if
        (delimiter? ch)
      (lazy-cons (assoc token :val (symbol text) :end ann)
        (token-seq cseq))
      (recur (rest cseq) (tappend token ch)))
    (= type :unknown)
    (if
        (delimiter? ch)
      (lazy-cons (assoc token :end ann) (token-seq cseq))
      (recur (rest cseq) (tappend token ch)))
    ))))

(defn token-seq-from-file
  "Reads a file f and produces a lazy sequence of tokens"
  [#^String f]
  (token-seq (char-seq-from-file f)))

(defn- exit
  "Exits from the clojure repl."
  ([]
     (exit 0))
  ([exitcode]
     (. System (exit exitcode))))

(defn- print-error
  "Displays an error message selected by err keyword, requires a token
  so that additional information can be provided to the user"
  [err token]
  (let [end (:end token) start (:start token)
    fname (:fname start) line (:line start) col (:col start)]
    ;;(prn token)
    (cond
     (= err :eof)
     (do
       (println
    (str "Unmatched left parenthesis, "
         fname ":" line ":" col)))
     (= err :rparen)
     (println (str "Unmatched right parenthesis, "
           fname ":" line ":" col))
     (= err :numformat)
     (println (str "Invalid number format: \"" (:txt token)
           "\", " fname ":" line ":" col))
     :else
     (println (str "Unknown error, "
           fname ":" line ":" col)))
    ;; (exit 1)
    ))

(defn- read-helper
  [tseq vec root? single?]
  (let [token (first tseq) type (:type token) ann (:end token)]
    ;;(prn token)
    (if token
      (cond
       (= type :lparen)
       (let [res (read-helper
          (rest tseq)
          {:type :list :val (list) :start (:start token)}
          false false)
         nvec (dissoc res :tseq :eof)
         ntseq (:tseq res)]
     (when (:eof res)
       (print-error :eof token))
     (let [val (if (= (count (:val nvec)) 0)
             (assoc nvec :type :list :val nil)
             nvec)]
       (if single?
         (assoc (val-conj vec val) :tseq ntseq)
         (recur (rest ntseq) (val-conj vec val) root? false))))
       (= type :rparen)
       (if root?
     (do (print-error :rparen token)
         (assoc vec :tseq tseq :end ann :val (reverse (:val vec))))
     (assoc vec :tseq tseq :end ann :val (reverse (:val vec))))
       (:expand token)
       (let [res (read-helper (rest tseq)
                   {:type :list :val (list token)}
                   false true)
         nvec (dissoc res :tseq)
         ntseq (:tseq res)]
     (if single?
       (assoc (val-conj vec nvec) :tseq ntseq)
       (recur (rest ntseq) (val-conj vec nvec) root? false)))
       (contains? token :error)
       (do (print-error (:error token) token)
       (if single?
         (assoc (val-conj vec token) :tseq tseq)
         (recur (rest tseq) (val-conj vec token) root? false)))
       :else
       (if single?
     (assoc (val-conj vec token) :tseq tseq)
     (recur (rest tseq) (val-conj vec token) root? false)))
      (assoc vec :eof true :val (reverse (:val vec))))))

(defn read
  "Consumes a sequence of tokens as returned by token-seq and produces
  a syntax tree. Note that this function attempts to read the whole
  token sequence"
  ([]
     (read (token-seq (char-seq *in*))))
  ([tseq]
     (dissoc
      (read-helper tseq
            {:type :list :val (list)}
            true false)
      :tseq)))

(defn read-form-seq
  "Consumes a sequence of tokens as returned by token-seq and produces
  a lazy sequence of syntax trees. Each syntax tree is single top-level
  form. Note that this function attemtps to read the whole top-level form."
  ([]
     (read-form-seq (token-seq (char-seq *in*)) true))
  ([tseq root?]
     (when tseq
       (let [form
         (read-helper tseq {:type :list :val (list)} root? true)]
     (lazy-cons
         (first (:val form))
       (read-form-seq (rest (:tseq form)) root?))))))

(defn read-file
  "Reads a file fname and returns a syntax tree"
  [#^String fname]
  (read (token-seq-from-file fname)))

(def global-environment
     #^{:private true}
     {
      ;;(symbol "#f") false
      ;;(symbol "#t") true
      ;;'a {:val 1 :type :number}
      ;;'b {:body
      ;;  [{:val [{:val 'display :type :symbol} {:val 'n :type :symbol}] :type :list}
      ;;   {:val [{:val (symbol "+") :type :symbol} {:val 'n :type :symbol} {:val 'n :type :symbol}] :type :list}]
      ;;  :arg-list
      ;;  [{:val 'n :type symbol}]
      ;;  :type :fun}
      (symbol "+") {:val prim_add :type :primitive-fun}
      (symbol "-") {:val prim_sub :type :primitive-fun}
      (symbol "*") {:val prim_mul :type :primitive-fun}
      (symbol "/") {:val prim_div :type :primitive-fun}
      (symbol "=") {:val prim_eq :type :primitive-fun}
      (symbol ">") {:val prim_gt :type :primitive-fun}
      (symbol "<") {:val prim_lt :type :primitive-fun}
;;      (symbol "cons") {:val prim_cons :type :primitive-fun}
;;      (symbol "car") {:val prim_car :type :primitive-fun}
;;      (symbol "cdr") {:val prim_cdr :type :primitive-fun}
      (symbol "display") {:val prim_display :type :primitive-fun}
      (symbol "write") {:val prim_write :type :primitive-fun}
      :parent nil
      :level 0
      :def-ok? true
      :tail? false
      })

(defn repl
  "Scheme Read-Eval-Print-Loop function"
  ([]
     (let [boot (read-file "boot.scm")
       result (eval-sequence-top
           (:val boot)
           global-environment)
       env (:env result)]
       (comment
     (pprint (dissoc result :env))
     (pprint env)
     )
       (prompt-for-input)
       (repl (read-form-seq) env)))
  ([sseq env]
     (when sseq
       (let [output (eval (first sseq) env)
         val (dissoc output :env)
         env (:env output)]
     ;;(let [output (first sseq)]
     ;;(pprint (first sseq))
     (output-prompt)
     (print-exp true output)
     (comment
       (newline)
       (pprint (:env output))
       (newline)
       (pprint (dissoc output :env))
       )
     (prompt-for-input)
     (recur (rest sseq) env)))))

(repl)

;(exit)
