open Types
  
let encode_queries ql p =
  let ql', p' = 
    List.fold_left (fun (ql_done, p) q ->
      match q with
      | QSecret(v, pub_vars, Reachability one_session) ->
	  let index_types = List.map (fun ri -> ri.ri_type) v.args_at_creation in
	  (* Build the new query adv_has_v(idx) ==> false *)
	  let adv_has_event =
	    Terms.create_event (Terms.fresh_id ("adv_has_"^v.sname)) []
	  in
          (* Adding the event to Stringmap.env so that it can be used in the "focus" command *)
	  Stringmap.env := Stringmap.StringMap.add adv_has_event.f_name (Stringmap.EEvent adv_has_event) (!Stringmap.env);
	  let event_var =
	    Terms.create_binder "i" Settings.t_bitstring []
	  in
	  let q' = QEventQ([false, Terms.app adv_has_event [Terms.term_from_binder event_var]],
			   QTerm (Terms.make_false()), pub_vars)
	  in

	  let reveal_info =
	    if one_session || index_types = [] then
	      None
	    else
	      let reveal_param =
		{ pname = Terms.fresh_id "Nreveal";
		  psize = Settings.psize_DEFAULT }
	      in
	      let ty_reveal_param = Terms.type_for_param reveal_param in
	      let reveal_repl_idx =
		Terms.create_repl_index "ireveal" ty_reveal_param
	      in
	      let reveal_idx =
		List.map (fun ty ->
		  Terms.create_binder "u" ty [reveal_repl_idx]
		    ) index_types
	      in
	      let reveal_var =
		Terms.create_binder "reveal" Settings.t_bool [reveal_repl_idx]
	      in
	      let reveal_query_process =
		let reveal_ch = { cname = Terms.fresh_id "c_reveal" } in
		let make_reveal_ch() = (reveal_ch, [Terms.term_from_repl_index reveal_repl_idx]) in
		
		let make_idx() =
		  List.map Terms.term_from_binder reveal_idx
		in
		let out_proc = Terms.oproc_from_desc (Output(make_reveal_ch(), Terms.build_term_type v.btype (Var(v, make_idx())), Terms.iproc_from_desc Nil)) in
		let find_proc =
		  Terms.oproc_from_desc
		    (Find([[],[(v, make_idx())],Terms.make_true(), Terms.oproc_from_desc (Let(PatVar reveal_var, Terms.make_true(), out_proc, Terms.oproc_from_desc Yield))],
			  Terms.oproc_from_desc Yield, Nothing))
		in
		let pat_input =
		  let f = Settings.get_tuple_fun index_types in
		  PatTuple(f, List.map (fun v -> PatVar v) reveal_idx)
		in
		let input_proc =
		  Terms.iproc_from_desc (Input(make_reveal_ch(), pat_input, find_proc))
		in
		Terms.iproc_from_desc (Repl(reveal_repl_idx, input_proc))
	      in
	      Some (reveal_repl_idx, reveal_idx, reveal_var, reveal_query_process)
	  in
	  
	  let test_query_process =
	    let test_param =
	      { pname = Terms.fresh_id "Ntest";
		psize = Settings.psize_DEFAULT }
	    in
	    let ty_test_param = Terms.type_for_param test_param in
	    let test_repl_idx =
	      Terms.create_repl_index "itest" ty_test_param
	    in
	    let test_idx =
	      List.map (fun ty ->
		Terms.create_binder "u" ty [test_repl_idx]
		  ) index_types
	    in
	    let test_var =
	      Terms.create_binder v.sname v.btype [test_repl_idx]
	    in
	    let make_idx() =
	      List.map Terms.term_from_binder test_idx
	    in
	    let test_cond = 
	      Terms.make_equal
		(Terms.term_from_binder test_var)
		(Terms.build_term_type v.btype (Var(v, make_idx())))
	    in
	    let tupf = Settings.get_tuple_fun [ty_test_param] in
	    let tcur_array =
	      Terms.app tupf [Terms.term_from_repl_index test_repl_idx]
	    in
	    let event_proc =
	      Terms.oproc_from_desc (EventP(Terms.app adv_has_event [tcur_array], Terms.oproc_from_desc Yield))
	    in
	    let find_proc =
	      Terms.oproc_from_desc
		(Find([[],[(v, make_idx())],test_cond, event_proc],
		      Terms.oproc_from_desc Yield, Nothing))
	    in
	    let find2_proc =
	      match reveal_info with
	      | None -> find_proc
	      | Some(reveal_repl_idx, reveal_idx, reveal_var, _) ->
		  let find_idx_var = Terms.create_binder "u" reveal_repl_idx.ri_type [test_repl_idx] in
		  let find_idx = Terms.create_repl_index "ri"  reveal_repl_idx.ri_type in
		       
		  Terms.oproc_from_desc
		    (Find([ [find_idx_var, find_idx],
			    (reveal_var, [Terms.term_from_repl_index find_idx])::(List.map (fun ridx -> (ridx, [Terms.term_from_repl_index find_idx])) reveal_idx),
			    Terms.make_and_list (List.map2 (fun ridx tidx ->
			      Terms.make_equal (Terms.term_from_binderref (ridx, [Terms.term_from_repl_index find_idx]))
				(Terms.term_from_binder tidx)) reveal_idx test_idx),
			    Terms.oproc_from_desc Yield],
			  find_proc, Nothing))
	    in
	    let pat_input =
	      if test_idx = [] then
		PatVar test_var
	      else
		let f = Settings.get_tuple_fun (v.btype::index_types) in
		PatTuple(f, (PatVar test_var)::(List.map (fun v -> PatVar v) test_idx))
	    in
	    let input_proc =
	      Terms.iproc_from_desc (Input(({ cname = Terms.fresh_id "c_test" }, [Terms.term_from_repl_index test_repl_idx]), pat_input, find2_proc))
	    in
	    Terms.iproc_from_desc (Repl(test_repl_idx, input_proc))
	  in
	  let p' =
	    Terms.iproc_from_desc (Par(p, test_query_process))
	  in
	  let p'' =
	    match reveal_info with
	    | None -> p'
	    | Some (_,_,_,reveal_query_process) ->
		Terms.iproc_from_desc (Par(p', reveal_query_process))
	  in
	  (q'::ql_done, p'') 
      | _ ->
	  (q::ql_done, p)
	    ) ([],p) ql
  in
  List.rev ql', p'
