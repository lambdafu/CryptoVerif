open Types

(* Function to call by default in case of matching error *)

val default_match_error : unit -> 'a

(* [match_funapp match_term get_var_link match_error simp_facts next_f t t' state]
   matches [t] and [t']; [t] must be FunApp, otherwise matching
   is considered to fail. The other cases must have been handled previously.

   [match_term]: [match_term next_f t1 t2 state] matches [t1] with [t2];
   calls [next_f state'] when the match succeeds; raises NoMatch when it
   fails. It must clean up the links it has put at least when it fails.
   (When it succeeds, the cleanup is optional.)

   [get_var_link]: [get_var_link t state] returns [Some (link, allow_neut)]
   when [t] is variable that can be bound by a product of terms,
   [link] is the current contents of the link of that variable,
   [allow_neut] is true if and only if the variable may be bound to
   the neutral element (provided there is a neutral element for the
   product); it returns [None] otherwise.

   [match_error]: [match_error()] is called in case of matching error.
   (In most cases, [match_error] should be [default_match_error],
   which raises the [NoMatch] exception.)

   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.

   [next_f]: [next_f state'] is called when the matching succeeds,
   that is, the variables in [t] are linked so that [\sigma t = t'].
   [next_f] can raise [NoMatch] to force the function to look for
   another matching.
*)

val match_funapp :
  (('b -> 'a) -> term -> term -> 'b -> 'a) ->
  (term -> 'b -> (linktype * bool) option) ->
  (unit -> 'a) -> 
  simp_facts ->
  ('b -> 'a) -> term -> term -> 'b -> 'a

(* [match_assoc_subterm match_term get_var_link next_f simp_facts prod l1 l2 state]
   matches the lists of terms [l1] and [l2] modulo associativity of the product
   function [prod].
   More precisely, it calls [next_f left_rest right_rest state'] after linking variables in [l1]
   so that [left_rest. \sigma l1 . right_rest = l2] modulo associativity.
   [match_term], [get_var_link], [simp_facts] are as in the function
   [match_funapp] above.
   *)

val match_assoc_subterm :
  (('b -> 'a) -> term -> term -> 'b -> 'a) ->
  (term -> 'b -> (linktype * bool) option) ->
  (term list -> term list -> 'b -> 'a) ->
  simp_facts ->
  funsymb -> term list -> term list -> 'b -> 'a

(* [match_AC match_term get_var_link match_error next_f simp_facts prod allow_rest l1 l2 state]
   matches the lists of terms [l1] and [l2] modulo associativity and commutativity
   of the product function [prod].
   [allow_rest] is true when one is allowed to match only a sublist of [l2] with [l1].
   When [allow_rest] is false, [match_AC] calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo AC. 
   When [allow_rest] is true, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo AC. 

   [match_term], [get_var_link], [match_error], [simp_facts] are as in the function
   [match_funapp] above.
*)

val match_AC :
  (('b -> 'a) -> term -> term -> 'b -> 'a) ->
  (term -> 'b -> (linktype * bool) option) ->
  (unit -> 'a) -> 
  (term list -> 'b -> 'a) ->
  simp_facts ->
  funsymb -> bool -> term list -> term list -> 'b -> 'a

(* [match_term_list match_term next_f l l' state] matches the lists of terms
   [l] and [l'], using [match_term] to match individual terms.
   [next_f state'] is called when the matching succeeds.
   It can raise [NoMatch] to force the function to look for
   another matching. *)

val match_term_list :
  (('b -> 'a) -> term -> term -> 'b -> 'a) ->
  ('b -> 'a) -> term list -> term list -> 'b -> 'a

(* Matching with advice, for use in transf_crypto.ml *)

(* [match_assoc_advice_subterm match_term explicit_value get_var_link is_var_inst next_f simp_facts prod l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f left_rest right_rest state']  after linking variables in [l1]
   so that [left_rest. \sigma l1 . right_rest = l2] modulo associativity.
   [left_rest] and [right_rest] may be empty. 

   [match_term]: [match_term next_f t1 t2 state] matches [t1] with [t2];
   calls [next_f state'] when the match succeeds; raises NoMatch when it
   fails. It must clean up the links it has put at least when it fails.
   (When it succeeds, the cleanup is optional.)

   [explicit_value]: [explicit_value t state] returns a state in which 
   the advice needed to instantiate the variable [t] has been recorded.
   Causes an internal error when [t] is not a variable.

   [get_var_link]: [get_var_link t state] returns [Some (link, allow_neut)]
   when [t] is variable that can be bound by a product of terms,
   [link] is the current contents of the link of that variable,
   [allow_neut] is true if and only if the variable may be bound to
   the neutral element (provided there is a neutral element for the
   product); it returns [None] otherwise.

   [is_var_inst]: [is_var_inst t] returns [true] when [t] is a variable
   that can be instantiated by applying advice.

   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.

   [prod] is the product function symbol, which is associative or AC.
 *)

val match_assoc_advice_subterm :
  (('a -> 'b) -> term -> term -> 'a -> 'b) ->
  (term -> 'a -> 'a) ->
  (term -> 'a -> (linktype * bool) option) ->
  (term -> bool) ->
  (term list -> term list -> 'a -> 'b) ->
  simp_facts ->
  funsymb -> term list -> term list -> 'a -> 'b

(* [match_assoc_advice_pat_subterm match_term explicit_value get_var_link is_var_inst next_f simp_facts prod allow_full l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f state']  after linking variables in [l1]
   so that [\sigma l1 = left_rest . l2 . right_rest] modulo associativity.
   [left_rest] and [right_rest] are just ignored, they are not passed to [next_f].

   [allow_full] is true when [l2] may match the full list [l1], that is,
   [left_rest] and [right_rest] may both be empty. 

   [match_term], [explicit_value], [get_var_link], [is_var_inst], [simp_facts], [prod] 
   are as in the function [match_assoc_advice_subterm] above.   
 *)

val match_assoc_advice_pat_subterm :
  (('a -> 'b) -> term -> term -> 'a -> 'b) ->
  (term -> 'a -> 'a) ->
  (term -> 'a -> (linktype * bool) option) ->
  (term -> bool) ->
  ('a -> 'b) ->
  simp_facts ->
  funsymb -> bool -> term list -> term list -> 'a -> 'b

(* [match_AC_advice match_term explicit_value get_var_link is_var_inst next_f simp_facts prod allow_rest_pat allow_full allow_rest l1 l2 state]
   matches the lists [l1] and [l2] modulo AC. 
   When [allow_rest] and [allow_rest_pat] are false, it calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo AC. 
   When [allow_rest] is true and [allow_rest_pat] is false, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo AC. 
   When [allow_rest] is false and [allow_rest_pat] is true, it calls [next_f [] state']  after linking variables in [l1]
   so that [\sigma l1 = l2 . lrest] modulo AC. [lrest] is ignored, it is not passed to [next_f].

   [allow_rest_pat] is true when a subterm of the pattern in [l1] should match
   [l2], so that some elements of [l1] are allowed to remain unmatched.

   In case [allow_rest_pat] is true, [allow_full] is true when [l2] may match the full list [l1], that is, [lrest] may be empty.

   [allow_rest] is true when the pattern in [l1] should match a subterm of 
   the term in [l2], so that some elements of [l2] are allowed to remain unmatched.

   [match_term], [explicit_value], [get_var_link], [is_var_inst], [simp_facts], [prod] 
   are as in the function [match_assoc_advice_subterm] above.   
*)

val match_AC_advice :
  (('a -> 'b) -> term -> term -> 'a -> 'b) ->
  (term -> 'a -> 'a) ->
  (term -> 'a -> (linktype * bool) option) ->
  (term -> bool) ->
  (term list -> 'a -> 'b) ->
  simp_facts ->
  funsymb -> bool -> bool -> bool -> term list -> term list -> 'a -> 'b

(* [match_funapp_advice match_term explicit_value get_var_link is_var_inst next_f simp_facts t t' state]
   matches [t] with [t'] when they are function applications. More precisely,
   it calls [next_f state'] after linking variables in [t] such that [\sigma t = t'].

   [match_term], [explicit_value], [get_var_link], [is_var_inst], [simp_facts]
   are as in the function [match_assoc_advice_subterm] above.   
 *)

val match_funapp_advice :
  (('a -> 'b) -> term -> term -> 'a -> 'b) ->
  (term -> 'a -> 'a) ->
  (term -> 'a -> (linktype * bool) option) ->
  (term -> bool) -> ('a -> 'b) -> 
  simp_facts ->
  term -> term -> 'a -> 'b

