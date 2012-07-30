(* Representation of sets of binders by a hash table, using chaining.
   I would have liked to use the standard Caml hash table module,
   but I could not because of a recursivity in types: the type binder
   contains sets of binders. So I had to reimplement it *)

open Types

let hash b =
  if b.vname == 0 then Hashtbl.hash b.sname else b.vname

let empty = 
  { nelem = 0; table = Array.make 1 [] }

let add s elem =
  let s = 
    if s == empty then
      { nelem = 0; table = Array.make 7 [] }
    else
      s
  in
  begin
    let nslot = Array.length s.table in
    let index = (hash elem) mod nslot in
    if not (List.memq elem s.table.(index)) then
      begin
	s.nelem <- s.nelem+1;
	s.table.(index) <- elem :: s.table.(index);
	(* filling factor at most 3 *)
	if s.nelem > 3 * nslot then
	  let new_nslot = 3 * nslot in
	  let new_table = Array.make new_nslot [] in
	  for i = 0 to nslot - 1 do
	    List.iter (fun elem ->
	      let new_index = (hash elem) mod new_nslot in
	      new_table.(new_index) <- elem :: new_table.(new_index)) s.table.(i)
	  done;
	  s.table <- new_table
      end
  end;
  s
    
let mem s elem =
  List.memq elem s.table.((hash elem) mod (Array.length s.table))
