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

