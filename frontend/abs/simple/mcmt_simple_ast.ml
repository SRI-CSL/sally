open Simple_ast;;

type mcmt_transition_system =
  { name : string;
    decls : decl list;
    current_sv_decls: decl list;
    next_sv_decls: decl list;
    init: expr;
    trans: expr;
    invs: expr list }
