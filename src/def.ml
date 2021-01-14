open Types

(* Empty tree of definition dependances 
   The treatment of TestE/FindE/LetE/ResE is necessary: build_def_process
   is called in check.ml.
*)


let rec empty_def_term t =
  t.t_facts <- None;
  match t.t_desc with
    Var(b,l) ->
      b.def <- [];
      empty_def_term_list l
  | ReplIndex _ -> ()
  | FunApp(_,l) ->
      empty_def_term_list l
  | TestE(t1,t2,t3) ->
      empty_def_term t2;
      empty_def_term t3;
      empty_def_term t1
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (b1,b2) -> b1.def <- []) bl;
	empty_def_term_def_list def_list;
	empty_def_term t1;
	empty_def_term t2) l0;
      empty_def_term t3;
  | LetE(pat, t1, t2, topt) ->
      empty_def_pattern pat;
      empty_def_term t1;
      empty_def_term t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> empty_def_term t3
      end
  | ResE(b,t) -> b.def <- []; empty_def_term t
  | EventAbortE _ -> ()
  | EventE(t,p) ->
      empty_def_term t;
      empty_def_term p
  | GetE(tbl,patl,topt,p1,p2) ->
      List.iter empty_def_pattern patl;
      (match topt with None -> () | Some t -> empty_def_term t);
      empty_def_term p1;
      empty_def_term p2
  | InsertE(tbl,tl,p) -> 
      List.iter empty_def_term tl;
      empty_def_term p

and empty_def_term_list l = List.iter empty_def_term l

and empty_def_br (b,l) = b.def <- []; empty_def_term_list l

and empty_def_term_def_list def_list = 
  List.iter empty_def_br def_list

and empty_def_pattern = function
    PatVar b -> b.def <- []
  | PatTuple (f,l) -> List.iter empty_def_pattern l
  | PatEqual t -> empty_def_term t

let rec empty_def_process p = 
  p.i_facts <- None;
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      empty_def_process p1;
      empty_def_process p2
  | Repl(b,p) ->
      empty_def_process p
  | Input((c,tl),pat,p) ->
      List.iter empty_def_term tl;
      empty_def_pattern pat;
      empty_def_oprocess p

and empty_def_oprocess p = 
  p.p_facts <- None;
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      b.def <- [];
      empty_def_oprocess p
  | Test(t,p1,p2) ->
      empty_def_term t;
      empty_def_oprocess p1;
      empty_def_oprocess p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b1,b2) -> b1.def <- []) bl;
	empty_def_term_def_list def_list;
	empty_def_term t;
	empty_def_oprocess p1) l0;
      empty_def_oprocess p2
  | Output((c,tl),t',p) ->
      List.iter empty_def_term tl;
      empty_def_term t';
      empty_def_process p
  | Let(pat,t,p1,p2) ->
      empty_def_term t;
      empty_def_pattern pat;
      empty_def_oprocess p1;
      empty_def_oprocess p2
  | EventP(t,p) ->
      empty_def_term t;
      empty_def_oprocess p
  | Get(tbl,patl,topt,p1,p2) ->
      List.iter empty_def_pattern patl;
      (match topt with None -> () | Some t -> empty_def_term t);
      empty_def_oprocess p1;
      empty_def_oprocess p2
  | Insert(tbl,tl,p) -> 
      List.iter empty_def_term tl;
      empty_def_oprocess p

let rec empty_def_fungroup = function
    ReplRestr(repl_opt, restr, funlist) ->
      List.iter (fun (b,_) -> b.def <- []) restr;
      List.iter empty_def_fungroup funlist
  | Fun(ch, args, res, priority) ->
      List.iter (fun b -> b.def <- []) args;
      empty_def_term res

let empty_def_member l =
  List.iter (fun (fg, mode) -> empty_def_fungroup fg) l


(* Build tree of definition dependences
   The treatment of TestE/FindE/LetE/ResE is necessary: build_def_process
   is called in check.ml.

   The value of elsefind_facts is correct even if the game has not been expanded:
   we correctly discard elsefind_facts when their defined condition refers
   to a variable defined in a term.
   *)

let find_list_to_elsefind accu l =
  List.fold_left (fun ((fact_accu, else_find_accu) as accu) ((bl, def_list, t1,_):'a findbranch) ->
    if Terms.check_simple_term t1 then
      if bl == [] && def_list == [] then
	((Terms.make_not t1)::fact_accu, else_find_accu)
      else
	(fact_accu, (List.map snd bl, def_list, t1)::else_find_accu)
    else
      accu) accu l

let rec add_vars_from_pat accu = function
    PatVar b -> Terms.addq accu b
  | PatEqual t -> accu
  | PatTuple (f,l) -> add_vars_from_pat_list accu l

and add_vars_from_pat_list accu = function
    [] -> accu
  | (a::l) -> add_vars_from_pat_list (add_vars_from_pat accu a) l

let rec def_vars_term accu t = 
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> def_vars_term_list accu l
  | ReplIndex i -> accu
  | TestE(t1,t2,t3) -> 
      def_vars_term (def_vars_term (def_vars_term accu t1) t2) t3
  | FindE(l0, t3, _) ->
      let accu = ref (def_vars_term accu t3) in
      List.iter (fun (bl, def_list, t1, t2) ->
	(*Nothing to do for def_list: it contains only
          Var and Fun*)
	accu := Terms.unionq (List.map fst bl) (def_vars_term (def_vars_term (!accu) t1) t2)
	     ) l0;
      !accu
  | LetE(pat, t1, t2, topt) ->
      let accu' = match topt with
	None -> accu
      |	Some t3 -> def_vars_term accu t3 
      in
      def_vars_term (def_vars_pat (add_vars_from_pat (def_vars_term accu' t2) pat) pat) t1
  | ResE(b,t) ->
      Terms.addq (def_vars_term accu t) b
  | EventAbortE _ -> accu
  | EventE(t,p) ->
      def_vars_term (def_vars_term accu p) t
  | GetE(tbl,patl,topt,p1,p2) ->
      let accu' = match topt with
	None -> accu
      |	Some t -> def_vars_term accu t
      in
      def_vars_term (def_vars_term (def_vars_pat_list (add_vars_from_pat_list accu' patl) patl) p1) p2
  | InsertE(tbl,tl,p) ->
      def_vars_term_list (def_vars_term accu p) tl
      
and def_vars_term_list accu = function
    [] -> accu
  | (a::l) -> def_vars_term (def_vars_term_list accu l) a

and def_vars_pat accu = function
    PatVar b -> accu 
  | PatTuple (f,l) -> def_vars_pat_list accu l
  | PatEqual t -> def_vars_term accu t

and def_vars_pat_list accu = function
    [] -> accu
  | (a::l) -> def_vars_pat (def_vars_pat_list accu l) a

(* def_term is always called with  above_node.def_vars_at_def \subseteq def_vars
def_term returns a node n'. In this node n', we always have n'.def_vars_at_def \subseteq def_vars
Same property for def_term_list, def_term_def_list, def_pattern, def_pattern_list.
By induction. 
In cases ReplIndex, FindE, n' = above_node. 
In the other cases, we use the induction hypothesis. *)

let rec def_term event_accu cur_array above_node true_facts def_vars elsefind_facts t =
  if (t.t_facts != None) then
    Parsing_helper.internal_error "Two terms physically equal: cannot compute facts correctly";
  t.t_facts <- Some (cur_array, true_facts, elsefind_facts, def_vars, [], [], above_node);
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      let (above_node', _) = def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts l in
      above_node'
  | ReplIndex i -> above_node
  | TestE(t1,t2,t3) ->
      let true_facts' = t1 :: true_facts in
      let true_facts'' = (Terms.make_not t1) :: true_facts in
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t1 in
      ignore(def_term event_accu cur_array above_node' true_facts' def_vars elsefind_facts' t2);
      ignore(def_term event_accu cur_array above_node' true_facts'' def_vars elsefind_facts' t3);
      above_node'
  | FindE(l0,t3,find_info) ->
      let (true_facts_else, elsefind_facts_else) = 
	find_list_to_elsefind (true_facts, elsefind_facts) l0
      in
      let rec find_l seen = function
	  [] -> ()
	| ((bl,def_list,t1,t2) as cur_branch)::l ->
	    find_l (cur_branch::seen) l;
	    let vars = List.map fst bl in
	    let repl_indices = List.map snd bl in
	    let vars_terms = List.map Terms.term_from_binder vars in
            let (sure_facts_t1, sure_def_list_t1, elsefind_t1) = Info_from_term.def_vars_and_facts_from_term t1 in
	    let sure_facts_t1 = List.map (Terms.subst repl_indices vars_terms) sure_facts_t1 in
	    let sure_def_list_t1 = Terms.subst_def_list repl_indices vars_terms sure_def_list_t1 in
	    let elsefind_t1 = List.map (Terms.subst_else_find repl_indices vars_terms) elsefind_t1 in

	    let (true_facts', elsefind_facts_then) =
	      if find_info == Unique then
		(* When the find is Unique, I know that the other branches fail,
		   so I can add the corresponding elsefind facts *)
		find_list_to_elsefind (true_facts, elsefind_t1 @ elsefind_facts) (List.rev_append seen l)
	      else
		(true_facts, elsefind_t1 @ elsefind_facts)
	    in
            (* The variables defined in t are variables defined in conditions of find,
	       one cannot make array accesses to them, nor test their definition,
	       so they will not appear in defined conditions of elsefind_facts.
	       We need not take them into account to update elsefind_facts. *)
	    let elsefind_facts_then = List.map (Terms.update_elsefind_with_def vars) elsefind_facts_then in
	    let true_facts' = List.rev_append sure_facts_t1 true_facts' in
	    let accu = ref [] in
	    List.iter (Terms.close_def_subterm accu) def_list;
	    let def_list_subterms = !accu in 
	    let def_vars_t1 = def_list_subterms @ def_vars in
       	    let def_vars' =
              List.rev_append sure_def_list_t1
		(List.rev_append (Terms.subst_def_list repl_indices vars_terms def_list_subterms)
		   def_vars)
            in
	    let above_node' = { above_node = Some above_node; binders = vars; 
				true_facts_at_def = true_facts'; 
				def_vars_at_def = def_vars';
				elsefind_facts_at_def = elsefind_facts;
				future_binders = []; future_true_facts = []; 
				definition = DTerm t;
				definition_success = DTerm t2 } 
	    in
	    List.iter (fun b -> b.def <- above_node' :: b.def) vars;
	    ignore(def_term event_accu (repl_indices @ cur_array) 
		     (def_term_def_list event_accu cur_array above_node true_facts def_vars elsefind_facts def_list)
		     true_facts def_vars_t1 elsefind_facts t1);
	    ignore(def_term event_accu cur_array above_node' true_facts' def_vars' elsefind_facts_then t2)
      in
      find_l [] l0;
      ignore(def_term event_accu cur_array above_node true_facts_else def_vars elsefind_facts_else t3);
      above_node
  | LetE(pat, t1, t2, topt) ->
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t1 in
      let accu = ref [] in
      let (above_node'', elsefind_facts'') = def_pattern_ef accu event_accu cur_array above_node' true_facts def_vars elsefind_facts' pat in
      let true_facts' = ((match pat with PatVar _ -> Terms.make_let_equal | _ -> Terms.make_equal) (Terms.term_from_pat pat) t1) :: true_facts in
      let above_node''' = { above_node = Some above_node''; binders = !accu; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars;
			    elsefind_facts_at_def = elsefind_facts'';
			    future_binders = []; future_true_facts = []; 
			    definition = DTerm t;
			    definition_success = DTerm t2 } 
      in
      let elsefind_facts''' = List.map (Terms.update_elsefind_with_def (!accu)) elsefind_facts'' in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      ignore (def_term event_accu cur_array above_node''' true_facts' def_vars elsefind_facts''' t2);
      begin
	match topt with
	  None -> ()
	| Some t3 -> 
	    let true_facts' = 
	      try
		(Terms.make_for_all_diff (Terms.gen_term_from_pat pat) t1) :: true_facts
	      with Terms.NonLinearPattern -> true_facts
	    in
	    ignore(def_term event_accu cur_array above_node' true_facts' def_vars elsefind_facts'' t3)
      end;
      above_node'
  | ResE(b, t') ->
      let elsefind_facts' = List.map (Terms.update_elsefind_with_def [b]) elsefind_facts in
      let above_node' = { above_node = Some above_node; binders = [b]; 
			  true_facts_at_def = true_facts; 
			  def_vars_at_def = def_vars;
			  elsefind_facts_at_def = elsefind_facts;
			  future_binders = []; future_true_facts = []; 
			  definition = DTerm t;
			  definition_success = DTerm t' } 
      in
      b.def <- above_node' :: b.def;
      def_term event_accu cur_array above_node' true_facts def_vars elsefind_facts' t'
  | EventAbortE f ->
      begin
	match event_accu with
	  None -> ()
	| Some accu ->
	    let tupf = Settings.get_tuple_fun (List.map (fun ri -> ri.ri_type) cur_array) in
	    let idx = Terms.app tupf (List.map Terms.term_from_repl_index cur_array) in
	    let t' = Terms.build_term_type_occ Settings.t_bool t.t_occ (FunApp(f, [idx])) in
	    accu := (t', DTerm t) :: (!accu)
      end;
      above_node
  | EventE(t1,p) ->
      begin
	match event_accu with
	  None -> ()
	| Some accu -> accu := (t1, DTerm t) :: (!accu)
      end;
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t1 in
      def_term event_accu cur_array above_node' (t1 :: true_facts) def_vars elsefind_facts' p

  | GetE(tbl,patl,topt,p1,p2) ->
      let accu = ref [] in
      let above_node' = def_pattern_list accu event_accu cur_array above_node true_facts def_vars elsefind_facts patl in
      let above_node'' = 
        match topt with 
          Some t -> def_term event_accu cur_array above_node' true_facts def_vars elsefind_facts t
        | None -> above_node'
      in
      (* The variables defined in patl, topt are variables defined in conditions of find,
	 one cannot make array accesses to them, nor test their definition,
	 so they will not appear in defined conditions of elsefind_facts.
	 We need not update elsefind_facts. *)
      let elsefind_facts' = List.map (Terms.update_elsefind_with_def (!accu)) elsefind_facts in
      ignore (def_term event_accu cur_array above_node'' true_facts def_vars elsefind_facts' p1);
      ignore (def_term event_accu cur_array above_node true_facts def_vars elsefind_facts p2);
      above_node
        
  | InsertE(tbl,tl,p) ->
      let (above_node', elsefind_facts') = def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts tl in
      def_term event_accu cur_array above_node' true_facts def_vars elsefind_facts' p

	
(* same as [def_term] but additionally updates elsefind_facts to take into account
   the variables defined in [t] *) 
and def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t =
  let above_node' = def_term event_accu cur_array above_node true_facts def_vars elsefind_facts t in
  let vars_t = def_vars_term [] t in
  let elsefind_facts' = List.map (Terms.update_elsefind_with_def vars_t) elsefind_facts in
  (above_node', elsefind_facts')

(* [def_term_list_ef] also updates elsefind_facts to take into account
   the variables defined in the considered list of terms *)
and def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts = function
    [] -> (above_node, elsefind_facts)
  | (a::l) -> 
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts a in
      def_term_list_ef event_accu cur_array above_node' true_facts def_vars elsefind_facts' l

and def_term_def_list event_accu cur_array above_node true_facts def_vars elsefind_facts = function
    [] -> above_node
  | (b,l)::l' -> 
      let (above_node', elsefind_facts') = def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts l in
      def_term_def_list event_accu cur_array above_node' true_facts def_vars elsefind_facts' l'

and def_pattern accu event_accu cur_array above_node true_facts def_vars elsefind_facts = function
    PatVar b -> accu := b :: (!accu); above_node
  | PatTuple (f,l) -> def_pattern_list accu event_accu cur_array above_node true_facts def_vars elsefind_facts l
  | PatEqual t -> def_term event_accu cur_array above_node true_facts def_vars elsefind_facts t

(* same as [def_pattern] but additionally updates elsefind_facts to take into account
   the variables defined in [pat] *) 
and def_pattern_ef accu event_accu cur_array above_node true_facts def_vars elsefind_facts pat = 
  let above_node' = def_pattern accu event_accu cur_array above_node true_facts def_vars elsefind_facts pat in
  let vars_pat = def_vars_pat [] pat in
  let elsefind_facts' = List.map (Terms.update_elsefind_with_def vars_pat) elsefind_facts in
  (above_node', elsefind_facts')

and def_pattern_list accu event_accu cur_array above_node true_facts def_vars elsefind_facts = function
    [] -> above_node 
  | (a::l) -> 
      let (above_node', elsefind_facts') = def_pattern_ef accu event_accu cur_array above_node true_facts def_vars elsefind_facts a in
      def_pattern_list accu event_accu cur_array above_node' true_facts def_vars elsefind_facts' l

(* def_process is always called with above_node.def_vars_at_def \subseteq def_vars
   By induction, also using the properties of def_term, ...
   One case in which the two values are different is in the condition of find:
   def_vars contains the def_list, which is not included in above_node.def_vars_at_def. *)

let rec def_process event_accu cur_array above_node true_facts def_vars p' =
  if p'.i_facts != None then
    Parsing_helper.internal_error "Two processes physically equal: cannot compute facts correctly";
  p'.i_facts <- Some (cur_array, true_facts, [], def_vars, [], [], above_node);
  match p'.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      def_process event_accu cur_array above_node true_facts def_vars p1;
      def_process event_accu cur_array above_node true_facts def_vars p2
  | Repl(b,p) ->
      (* A node is needed here, even if the replication defines no
	 binders, because I rely on the node to locate the
	 replication in Simplify.CompatibleDefs.check_compatible *)
      let above_node' = { above_node = Some above_node; binders = [];
                          true_facts_at_def = true_facts;
                          def_vars_at_def = def_vars;
                          elsefind_facts_at_def = [];
                          future_binders = []; future_true_facts = []; 
                          definition = DInputProcess p';
			  definition_success = DInputProcess p }
      in
      def_process event_accu (b::cur_array) above_node' true_facts def_vars p
  | Input((c,tl),pat,p) ->
      let (above_node',_) = def_term_list_ef event_accu cur_array above_node true_facts def_vars [] tl in
      let accu = ref [] in
      let above_node'' = def_pattern accu event_accu cur_array above_node' true_facts def_vars [] pat in
      (* is_find_unique uses this node to test whether two variables are defined
	 in the same input/output block, so it's important to generate this
	 node even if the pattern pat defines no variable. *)
      let above_node''' = { above_node = Some above_node''; binders = !accu; 
			    true_facts_at_def = true_facts; 
			    def_vars_at_def = def_vars;
			    elsefind_facts_at_def = [];
			    future_binders = []; future_true_facts = []; 
			    definition = DInputProcess p';
			    definition_success = DProcess p } 
      in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      let (fut_binders, fut_true_facts) = 
	def_oprocess event_accu cur_array above_node''' true_facts def_vars [] p
      in
      above_node'''.future_binders <- fut_binders;
      above_node'''.future_true_facts <- fut_true_facts

and def_oprocess event_accu cur_array above_node true_facts def_vars elsefind_facts p' =
  if p'.p_facts != None then
    Parsing_helper.internal_error "Two processes physically equal: cannot compute facts correctly";
  p'.p_facts <- Some (cur_array, true_facts, elsefind_facts, def_vars, [], [], above_node);
  let (fut_binders, fut_true_facts) as result =
  begin
  match p'.p_desc with
    Yield -> 
      ([],[])
  | EventAbort f -> 
      begin
	match event_accu with
	  None -> ()
	| Some accu -> 
	    let tupf = Settings.get_tuple_fun (List.map (fun ri -> ri.ri_type) cur_array) in
	    let idx = Terms.app tupf (List.map Terms.term_from_repl_index cur_array) in
	    let t = Terms.build_term_type_occ Settings.t_bool p'.p_occ (FunApp(f, [idx])) in
	    accu := (t, DProcess p') :: (!accu)
      end;
      ([],[])
  | Restr(b,p) ->
      let elsefind_facts' = List.map (Terms.update_elsefind_with_def [b]) elsefind_facts in
      let above_node' = { above_node = Some above_node; binders = [b]; 
			  true_facts_at_def = true_facts; 
			  def_vars_at_def = def_vars;
			  elsefind_facts_at_def = elsefind_facts;
			  future_binders = []; future_true_facts = []; 
			  definition = DProcess p';
			  definition_success = DProcess p } 
      in
      b.def <- above_node' :: b.def;
      let (fut_binders, fut_true_facts) = 
	def_oprocess event_accu cur_array above_node' true_facts def_vars elsefind_facts' p
      in
      above_node'.future_binders <- fut_binders;
      above_node'.future_true_facts <- fut_true_facts;
      (b::fut_binders, fut_true_facts)
  | Test(t,p1,p2) ->
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t in
      let true_facts' = t :: true_facts in
      let true_facts'' = (Terms.make_not t) :: true_facts in
      let (fut_binders1, fut_true_facts1) = 
	def_oprocess event_accu cur_array above_node' true_facts' def_vars elsefind_facts' p1
      in
      let (fut_binders2, fut_true_facts2) = 
	def_oprocess event_accu cur_array above_node' true_facts'' def_vars elsefind_facts' p2
      in
      (Terms.intersect (==) fut_binders1 fut_binders2, 
       Terms.intersect Terms.equal_terms fut_true_facts1 fut_true_facts2)
  | Find(l0,p2,find_info) ->
      let (true_facts', elsefind_facts') = 
	find_list_to_elsefind (true_facts, elsefind_facts) l0
      in
      let (fut_binders2, fut_true_facts2) = 
	def_oprocess event_accu cur_array above_node true_facts' def_vars elsefind_facts' p2
      in
      let rec find_l seen = function
	  [] -> (fut_binders2, fut_true_facts2)
	| ((bl,def_list,t,p1) as cur_branch)::l ->
	    let (fut_bindersl, fut_true_factsl) = find_l (cur_branch::seen) l in
	    let vars = List.map fst bl in
	    let repl_indices = List.map snd bl in
	    let vars_terms = List.map Terms.term_from_binder vars in
            let (sure_facts_t, sure_def_list_t, elsefind_t) = Info_from_term.def_vars_and_facts_from_term t in
	    let sure_facts_t = List.map (Terms.subst repl_indices vars_terms) sure_facts_t in
	    let sure_def_list_t = Terms.subst_def_list repl_indices vars_terms sure_def_list_t in
	    let elsefind_t = List.map (Terms.subst_else_find repl_indices vars_terms) elsefind_t in
	    
	    let (true_facts', elsefind_facts_then) =
	      if find_info == Unique then
		(* When the find is Unique, I know that the other branches fail,
		   so I can add the corresponding elsefind facts *)
		find_list_to_elsefind (true_facts, elsefind_t @ elsefind_facts) (List.rev_append seen l)
	      else
		(true_facts, elsefind_t @ elsefind_facts)
	    in
            (* The variables defined in t are variables defined in conditions of find,
	       one cannot make array accesses to them, nor test their definition,
	       so they will not appear in defined conditions of elsefind_facts.
	       We need not take them into account to update elsefind_facts. *)
	    let elsefind_facts_then = List.map (Terms.update_elsefind_with_def vars) elsefind_facts_then in
	    let true_facts' = List.rev_append sure_facts_t true_facts' in
	    let accu = ref [] in
	    List.iter (Terms.close_def_subterm accu) def_list;
	    let def_list_subterms = !accu in 
	    let def_vars_t = def_list_subterms @ def_vars in
       	    let def_vars' =
              List.rev_append sure_def_list_t
                (List.rev_append (Terms.subst_def_list repl_indices vars_terms def_list_subterms)
                   def_vars)
            in
	    let above_node' = { above_node = Some above_node; binders = vars; 
				true_facts_at_def = true_facts'; 
				def_vars_at_def = def_vars';
				elsefind_facts_at_def = elsefind_facts;
				future_binders = []; future_true_facts = []; 
				definition = DProcess p';
			        definition_success = DProcess p1 } 
	    in
	    List.iter (fun b -> b.def <- above_node' :: b.def) vars;
	    ignore(def_term event_accu (repl_indices @ cur_array) 
		     (def_term_def_list event_accu cur_array above_node true_facts def_vars elsefind_facts def_list)
		     true_facts def_vars_t elsefind_facts t);
	    let (fut_binders1, fut_true_facts1) = 
	      def_oprocess event_accu cur_array above_node' true_facts' def_vars' elsefind_facts_then p1
	    in
	    above_node'.future_binders <- fut_binders1;
	    above_node'.future_true_facts <- fut_true_facts1;
	    (Terms.intersect (==) (vars @ fut_binders1) fut_bindersl,
	     Terms.intersect Terms.equal_terms fut_true_facts1 fut_true_factsl)
      in
      find_l [] l0
  | Output((c,tl),t',p) ->
      let (above_node', elsefind_facts') = def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts tl in
      let above_node'' = def_term event_accu cur_array above_node' true_facts def_vars elsefind_facts' t' in
      def_process event_accu cur_array above_node'' true_facts def_vars p;
      ([],[])
  | Let(pat,t,p1,p2) ->
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t in
      let accu = ref [] in
      let (above_node'', elsefind_facts'') = def_pattern_ef accu event_accu cur_array above_node' true_facts def_vars elsefind_facts' pat in
      let new_fact = (match pat with PatVar _ -> Terms.make_let_equal | _ -> Terms.make_equal) (Terms.term_from_pat pat) t in
      let true_facts' = new_fact :: true_facts in
      let elsefind_facts''' = List.map (Terms.update_elsefind_with_def (!accu)) elsefind_facts'' in
      let above_node''' = { above_node = Some above_node''; binders = !accu; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars;
			    elsefind_facts_at_def = elsefind_facts'';
			    future_binders = []; future_true_facts = []; 
			    definition = DProcess p';
			    definition_success = DProcess p1 } 
      in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      let (fut_binders1, fut_true_facts1) = 
	def_oprocess event_accu cur_array above_node''' true_facts' def_vars elsefind_facts''' p1
      in
      above_node'''.future_binders <- fut_binders1;
      above_node'''.future_true_facts <- fut_true_facts1;
      begin
	match pat, p2.p_desc with
	  PatVar _, Yield -> 
	    ((!accu) @ fut_binders1, new_fact :: fut_true_facts1)
	| _ -> 
	    let true_facts' = 
	      try
		(Terms.make_for_all_diff (Terms.gen_term_from_pat pat) t) :: true_facts
	      with Terms.NonLinearPattern -> true_facts
	    in
	    let (fut_binders2, fut_true_facts2) = 
	      def_oprocess event_accu cur_array above_node' true_facts' def_vars elsefind_facts'' p2
	    in
	    (Terms.intersect (==) ((!accu) @ fut_binders1) fut_binders2,
	     Terms.intersect Terms.equal_terms (new_fact :: fut_true_facts1) fut_true_facts2)
      end
  | EventP(t,p) ->
      begin
	match event_accu with
	  None -> ()
	| Some accu -> accu := (t, DProcess p') :: (!accu)
      end;
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t in
      let (fut_binders, fut_true_facts) = 
	def_oprocess event_accu cur_array above_node' (t :: true_facts) def_vars elsefind_facts' p
      in
      (fut_binders, t::fut_true_facts)
  | Get(tbl,patl,topt,p1,p2) ->
      let accu = ref [] in
      let above_node' = def_pattern_list accu event_accu cur_array above_node true_facts def_vars elsefind_facts patl in
      let above_node'' = 
        match topt with 
          Some t -> def_term event_accu cur_array above_node' true_facts def_vars elsefind_facts t
        | None -> above_node'
      in
      (* The variables defined in patl, topt are variables defined in conditions of find,
	 one cannot make array accesses to them, nor test their definition,
	 so they will not appear in defined conditions of elsefind_facts.
	 We need not update elsefind_facts. *)
      let elsefind_facts' = List.map (Terms.update_elsefind_with_def (!accu)) elsefind_facts in
      let (fut_binders1, fut_true_facts1) = 
	def_oprocess event_accu cur_array above_node'' true_facts def_vars elsefind_facts' p1
      in
      let (fut_binders2, fut_true_facts2) = 
	def_oprocess event_accu cur_array above_node true_facts def_vars elsefind_facts p2
      in
      (Terms.intersect (==) fut_binders1 fut_binders2, 
       Terms.intersect Terms.equal_terms fut_true_facts1 fut_true_facts2)
        
  | Insert(tbl,tl,p) ->
      let (above_node', elsefind_facts') = def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts tl in
      def_oprocess event_accu cur_array above_node' true_facts def_vars elsefind_facts' p
  end
  in
  p'.p_facts <- Some (cur_array, true_facts, elsefind_facts, def_vars, fut_true_facts, fut_binders, above_node);
  result

let build_def_process event_accu p =
  empty_def_process p;
  let st_node = { above_node = None; 
		  binders = []; 
		  true_facts_at_def = []; 
		  def_vars_at_def = []; 
		  elsefind_facts_at_def = [];
		  future_binders = []; future_true_facts = []; 
		  definition = DNone;
		  definition_success = DNone } 
  in
  def_process event_accu [] st_node [] [] p

let rec build_def_fungroup cur_array above_node = function
  | ReplRestr(repl_opt, restr, funlist) ->
      let above_node2 =
	Terms.set_def (List.map fst restr) DFunRestr DNone (Some above_node)
      in
      let cur_array' = Terms.add_cur_array repl_opt cur_array in
      List.iter (build_def_fungroup cur_array' above_node2) funlist
  | Fun(ch, args, res, priority) ->
      let above_node1 =
	Terms.set_def args DFunArgs DNone (Some above_node)
      in
      ignore(def_term None cur_array above_node1 [] [] [] res)

let build_def_member l = 
  let rec st_node = Terms.set_def [] DNone DNone None in
  List.iter (fun (fg, mode) -> build_def_fungroup [] st_node fg) l
