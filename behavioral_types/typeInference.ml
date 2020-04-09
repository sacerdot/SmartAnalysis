open MicroSolidity
open Types

let type_of ~max_args:_ ~max_stack:_ (_cfg : configuration) =
 ["foo",[],TExpr (TInt 0)]
