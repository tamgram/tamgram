type symbol_sort =
  [ `Cell
  | `Pub
  ]

type unary_op =
  [ `Persist
  | `Not
  ]

type binary_op =
  [ `Exp
  | `Eq
  | `Iff
  | `Imp
  | `Or
  | `And
  | `Plus
  | `Xor
  ]

type quantifier =
  [ `Ex
  | `All
  ]

type value =
  [ `Str of string
  | `T
  | `F
  ]

type macro = {
  arg_and_typs : Typ.term Binding.t list;
  ret_typ : Typ.term;
  body : term;
}

and fact_anno = [
  | `Plus
  | `Minus
]

and term =
  | T_value of value Loc.tagged
  | T_symbol of string Loc.tagged * symbol_sort
  | T_var of Path.t * Name.t * Typ.term option
  | T_tuple of Loc.t option * term list
  | T_app of Path.t * Name.t * term list * fact_anno option
  | T_unary_op of unary_op * term
  | T_binary_op of binary_op * term * term
  | T_cell_pat_match of string Loc.tagged * term
  | T_cell_assign of string Loc.tagged * term
  | T_name_as of term * string Loc.tagged
  | T_let of {
      binding : term Binding.t;
      next : term;
    }
  | T_let_macro of {
      binding : macro Binding.t;
      next : term;
    }
  | T_action of {
      fact : term;
      temporal : string Loc.tagged * Name.t;
    }
  | T_temporal_a_lt_b of {
      a : string Loc.tagged * Name.t;
      b : string Loc.tagged * Name.t;
    }
  | T_temporal_eq of {
      a : string Loc.tagged * Name.t;
      b : string Loc.tagged * Name.t;
    }
  | T_quantified of {
      loc : Loc.t option;
      quantifier : quantifier;
      quant : Typ.term Binding.t list;
      formula : term;
    }

type cell_data_shape =
  | S_value of value
  | S_pub of string
  | S_fresh of string * Name.t
  | S_var of string * Name.t
  | S_tuple of cell_data_shape list
  | S_app of string * Name.t * cell_data_shape list
  | S_unary_op of unary_op * cell_data_shape
  | S_binary_op of binary_op * cell_data_shape * cell_data_shape

type fact_sort =
  [ `Linear
  | `Persist
  ]

type fact = {
  sort : fact_sort;
  name : string Loc.tagged;
  args : term list;
}

type rule_binding =
  | R_let of term Binding.t
  | R_let_macro of {
      binding : macro Binding.t;
    }

type rule = {
  l : term list;
  vars_in_l : Typ.term Binding.t list;
  bindings_before_a : rule_binding list;
  a : term list;
  bindings_before_r : rule_binding list;
  r : term list;
}

type while_mode = [
  | `Matching
  | `Not_matching
]

type while_cell_match = {
  mode : while_mode;
  cell : string Loc.tagged;
  term : term;
  vars_in_term : unit Binding.t list;
}

type loop_mode = [
  | `While of while_cell_match
  | `Unconditional
]

type proc =
  | P_null
  | P_let of {
      binding : term Binding.t;
      next : proc;
    }
  | P_let_macro of {
      binding : macro Binding.t;
      next : proc;
    }
  | P_app of Path.t * Name.t * term list * proc
  | P_line of {
      tag : string Loc.tagged option;
      rule : rule;
      next : proc;
    }
  | P_branch of Loc.t option * proc list * proc
  | P_scoped of proc * proc
  | P_loop of loop
  | P_break of Loc.t option * string Loc.tagged option
  | P_continue of Loc.t option * string Loc.tagged option

and proc_macro = {
  arg_and_typs : Typ.term Binding.t list;
  body : proc;
}

and loop = {
  label : string Loc.tagged option;
  mode : loop_mode;
  proc : proc;
  next : proc;
}


type trace_quantifier =
  [ `All_traces
  | `Exists_trace
  ]

type pred_option = unit

type pred = {
  arity : int;
  options : pred_option list;
}

type lemma_attr =
  [ `Sources
  | `Reuse
  | `Use_induction
  | `Hide_lemma of string
  | `Heuristic of string
  ]

type lemma = {
  trace_quantifier : trace_quantifier;
  formula : term;
  attrs : lemma_attr Loc.tagged list;
}

type decl =
  | D_builtins of string Loc.tagged list
  | D_process of {
      binding : proc Binding.t;
    }
  | D_process_macro of proc_macro Binding.t
  | D_fun of int Binding.t
  | D_pred of pred Binding.t
  | D_ppred of pred Binding.t
  | D_apred of int Binding.t
  | D_papred of int Binding.t
  | D_let of {
      binding : term Binding.t;
    }
  | D_macro of {
      binding : macro Binding.t;
    }
  | D_equation of {
      binding : term Binding.t;
    }
  | D_lemma of {
      binding : lemma Binding.t;
    }
  | D_restriction of {
      binding : term Binding.t;
    }
  | D_rule of {
      binding : rule Binding.t;
    }
  | D_modul of string Loc.tagged * modul
  | D_open of Path.t
  | D_insert of Path.t

and modul = decl list
