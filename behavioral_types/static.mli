val normalize: MicroSolidity.configuration -> MicroSolidity.configuration

exception Unbounded of (MicroSolidity.address * MicroSolidity.any_method_decl) list

val get_bounds:
 MicroSolidity.configuration ->
  [`Bounds of ((MicroSolidity.address * MicroSolidity.any_method_decl) * int) list
  |`Unbounded of (MicroSolidity.address * MicroSolidity.any_method_decl) list
  ]

val pp_bounds:
  [`Bounds of ((MicroSolidity.address * MicroSolidity.any_method_decl) * int) list
  |`Unbounded of (MicroSolidity.address * MicroSolidity.any_method_decl) list
  ]
  -> string
