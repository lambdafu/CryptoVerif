;;
;; mode for .cv files 
;;

(defvar cryptoverif-kw '("new" "out" "channel" "if" "then" "else" "find" "orfind" "suchthat" "fun" "param" "forall" "equation" "builtin" "proba" "type" "equiv" "process" "let" "in" "query" "secret" "public_vars" "const" "set" "defined" "collision" "event" "time" "yield" "event_abort" "maxlength" "length" "max" "newChannel" "inj-event" "foreach" "do" "return" "def" "expand" "proof" "implementation" "get" "insert" "table" "letfun") "Cryptoverif keywords")

(defvar cryptoverif-builtin '("noninteractive" "bounded" "fixed" "large" "password" "compos" "data" "decompos" "projection" "uniform" "commut" "assoc" "AC" "assocU" "ACU" "ACUN" "group" "commut_group" "manual" "computational" "unchanged" "exist" "all" "useful_change" "unique" "cv_onesession" "real_or_random" "cv_real_or_random" "pred" "serial" "inverse" "random") "Cryptoverif builtins")

;; build optimal regular expression from list of keywords
;; 'words if for taking full words only, not subwords
(defvar cryptoverif-kw-regexp (regexp-opt cryptoverif-kw 'words))
(defvar cryptoverif-builtin-regexp (regexp-opt cryptoverif-builtin 'words))

(defvar cryptoverif-connectives-regexp "\|\|\\|&&\\|<-R\\|<-\\|==>\\|<=(\\|)=>\\|<=\\|:=\\|->\\|!")

(setq cryptoverifKeywords
 `((,cryptoverif-kw-regexp . font-lock-keyword-face)
   (,cryptoverif-builtin-regexp . font-lock-builtin-face)
   (,cryptoverif-connectives-regexp . font-lock-reference-face)
  )
)

(define-derived-mode cryptoverif-mode fundamental-mode
  (setq font-lock-defaults '(cryptoverifKeywords))
  (setq mode-name "Cryptoverif")

;; comment highlighting
  (modify-syntax-entry ?\( "()1" cryptoverif-mode-syntax-table)
  (modify-syntax-entry ?\) ")(4" cryptoverif-mode-syntax-table)
  (modify-syntax-entry ?* ". 23" cryptoverif-mode-syntax-table)

;; _ and ' belong to ordinary identifiers
  (modify-syntax-entry ?_ "w" cryptoverif-mode-syntax-table)
  (modify-syntax-entry ?' "w" cryptoverif-mode-syntax-table)
)

;;
;; mode for .ocv files (oracles mode)
;;

(defvar cryptoverifo-kw '("new" "if" "then" "else" "find" "orfind" "suchthat" "fun" "param" "forall" "equation" "builtin" "proba" "type" "equiv" "process" "let" "in" "query" "secret" "public_vars" "const" "set" "defined" "collision" "event" "time" "yield" "event_abort" "maxlength" "length" "max" "newOracle" "inj-event" "foreach" "do" "return" "def" "expand" "proof" "implementation" "get" "insert" "table" "letfun" "run") "Cryptoverif keywords")

(defvar cryptoverifo-kw-regexp (regexp-opt cryptoverifo-kw 'words))
;; the builtins are the same as in the .cv mode

(defvar cryptoverifo-connectives-regexp "\|\|\\|&&\\|<-R\\|<-\\|==>\\|<=(\\|)=>\\|<=\\|:=\\|->\\|!")

(setq cryptoverifoKeywords
 `((,cryptoverifo-kw-regexp . font-lock-keyword-face)
   (,cryptoverif-builtin-regexp . font-lock-builtin-face)
   (,cryptoverifo-connectives-regexp . font-lock-reference-face)
  )
)

(define-derived-mode cryptoverifo-mode fundamental-mode
  (setq font-lock-defaults '(cryptoverifoKeywords))
  (setq mode-name "Cryptoverif Oracles")

;; comment highlighting
  (modify-syntax-entry ?\( "()1" cryptoverifo-mode-syntax-table)
  (modify-syntax-entry ?\) ")(4" cryptoverifo-mode-syntax-table)
  (modify-syntax-entry ?* ". 23" cryptoverifo-mode-syntax-table)

;; _ and ' belong to ordinary identifiers
  (modify-syntax-entry ?_ "w" cryptoverifo-mode-syntax-table)
  (modify-syntax-entry ?' "w" cryptoverifo-mode-syntax-table)
)

;;
;; mode for .pcv files (compatibility CryptoVerif and ProVerif)
;;

(defvar pcv-kw '("new" "out" "channel" "if" "then" "else" "fun" "param" "forall" "equation" "proba" "type" "process" "let" "in" "query" "secret" "public_vars" "const" "set"  "event" "yield" "event_abort" "inj-event" "foreach" "do" "def" "expand" "proof" "implementation" "get" "insert" "table" "letfun" "suchthat" "not") "Cryptoverif and ProVerif common keywords")

(defvar pcv-bad-kw '("among" "choice" "clauses" "diff" "elimtrue" "find" "orfind" "equivalence" "fail" "free" "noninterf" "nounif" "or" "otherwise" "phase" "putbegin" "reduc" "sync" "weaksecret" "builtin" "equiv" "defined" "collision" "time" "maxlength" "length" "max" "newChannel" "return") "CryptoVerif- or ProVerif-only keywords")

(defvar pcv-builtin '("noninteractive" "bounded" "fixed" "large" "password" ;;type options (ignored in PV)
		      "data" "projection" "uniform" "typeConverter" ;; function options
		      "cv_onesession" "real_or_random" "cv_real_or_random" "pv_real_or_random" "pv_reachability" ;; query options
		      "pred" "serial" "inverse" "random" ;; implementation options (ignored in PV)
		      ) "Cryptoverif and ProVerif common builtins")

(defvar pcv-bad-builtin '("commut" "assoc" "AC" "assocU" "ACU" "ACUN" "group" "commut_group" ;; equation builtin options in CV
			  "manual" "computational" "unchanged" "exist" "all" "useful_change" ;; equiv options in CV
			  "unique" ;; find option in CV
			  "private" ;; in PV
			  "reachability" ;; query option not supported in CV
			  "memberOptim" "decompData" "decompDataSelect" "block" ;; predicate options
			  "attacker" "mess" ;; predicates
			  ) "CryptoVerif- or ProVerif-only builtins")

;; build optimal regular expression from list of keywords
;; 'words if for taking full words only, not subwords
(defvar pcv-kw-regexp (regexp-opt pcv-kw 'words))
(defvar pcv-builtin-regexp (regexp-opt pcv-builtin 'words))
(defvar pcv-bad-kw-regexp (regexp-opt pcv-bad-kw 'words))
(defvar pcv-bad-builtin-regexp (regexp-opt pcv-bad-builtin 'words))

(defvar pcv-connectives-regexp "\|\|\\|&&\\|<-R\\|<-\\|==>\\|<=\\|!")

(setq pcvKeywords
 `((,pcv-kw-regexp . font-lock-keyword-face)
   (,pcv-builtin-regexp . font-lock-builtin-face)
   (,pcv-connectives-regexp . font-lock-reference-face)
   (,pcv-bad-kw-regexp . font-lock-warning-face)
   (,pcv-bad-builtin-regexp . font-lock-warning-face)
  )
)

(define-derived-mode pcv-mode fundamental-mode
  (setq font-lock-defaults '(pcvKeywords))
  (setq mode-name "Pro-Crypto-Verif")

;; comment highlighting
  (modify-syntax-entry ?\( "()1" pcv-mode-syntax-table)
  (modify-syntax-entry ?\) ")(4" pcv-mode-syntax-table)
  (modify-syntax-entry ?* ". 23" pcv-mode-syntax-table)

;; _ and ' belong to ordinary identifiers
  (modify-syntax-entry ?_ "w" pcv-mode-syntax-table)
  (modify-syntax-entry ?' "w" pcv-mode-syntax-table)
)
