open Types

val move_array_equiv : Parsing_helper.extent -> binder list -> ident list -> equiv_gen

val generate : equiv_gen -> Ptree.equiv_call_t -> equiv_gen
