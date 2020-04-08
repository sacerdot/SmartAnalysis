val normalize: MicroSolidity.configuration -> MicroSolidity.configuration

exception Unbounded of (MicroSolidity.address * MicroSolidity.any_method_decl) list

val get_bounds:
 MicroSolidity.configuration ->
  ((MicroSolidity.address * MicroSolidity.any_method_decl) * int) list

val pp_bounds:
 ((MicroSolidity.address * MicroSolidity.any_method_decl) * int) list -> string
