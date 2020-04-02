open MicroSolidity

let rec retype_stm : type a b. (a,b) stm -> (a,[`Epsilon]) stm =
 function
    Epsilon as s -> s
  | ReturnRhs _ as s -> s
  | Return as s -> s
  | Revert as s -> s
  | Assign(lhs,rhs,cont) -> Assign(lhs,rhs,retype_stm cont)
  | IfThenElse(g,stma,stmb,cont) -> IfThenElse(g,stma,stmb,retype_stm cont)

let rec stm_concat : type a b c. (a,b) stm -> (a,c) stm -> (a,c) stm =
 fun stm1 stm2 ->
 match stm1 with
    Epsilon -> stm2
  | ReturnRhs _ as stm1 -> stm1
  | Return as stm1 -> stm1
  | Revert as stm1 -> stm1
  | Assign(lhs,rhs,cont) -> Assign(lhs,rhs,stm_concat cont stm2)
  | IfThenElse(g,stma,stmb,cont) ->
     let cont = stm_concat cont stm2 in
     IfThenElse(g,retype_stm (stm_concat stma cont),retype_stm (stm_concat stmb cont),Revert)

let rec norm_stm : type a b. (a,b) stm -> methods * (a,b) stm = fun stm ->
 match stm with
    Epsilon
  | ReturnRhs _
  | Return
  | Revert -> [],stm
  | Assign(lhs,rhs,cont) ->
     let meths,cont = norm_stm cont in
     meths,
     (match lhs,cont with
         LDiscard,Return -> ReturnRhs rhs
       | LVar v,ReturnRhs (Expr (Var v')) ->
          (match eq_tag (fst v) (fst v') with
              Some Refl when snd v = snd v' -> ReturnRhs rhs
            | _ -> Assign(lhs,rhs,cont))
       | _ -> Assign(lhs,rhs,cont))
  | IfThenElse(g,stm1,stm2,cont) ->
     let meths1,stm1 = norm_stm (retype_stm (stm_concat stm1 cont)) in
     let meths2,stm2 = norm_stm (retype_stm (stm_concat stm2 cont)) in
     meths1@meths2,IfThenElse(g,stm1,stm2,Revert)

let norm_block (Block(params,locals,stm)) =
 let meths,stm = norm_stm stm in
 meths,Block(params,locals,stm)

let rec norm_methods =
 function
    [] -> []
  | AnyMethodDecl(name,block,payable)::tl ->
     let meths,block = norm_block block in
     meths @ [AnyMethodDecl(name,block,payable)] @ norm_methods tl

let norm_a_contract (AContract(addr,meths,fallback,fields)) =
 let meths1 = norm_methods meths in
 let meths2,fallback =
  match fallback with
     None -> [],None
   | Some fb ->
      let meths2,fb = norm_block fb in
       meths2,Some fb in
 AContract(addr,meths1@meths2,fallback,fields)

let normalize =
 List.map norm_a_contract
