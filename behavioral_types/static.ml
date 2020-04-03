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

type aux = Aux : 'a lhs option * 'a tagged_expr -> aux

let rec norm_stm : type a b. (a,b) meth -> b var_list -> 'c var_list -> bool -> (a,[`Return]) stm -> methods * (a,[`Return]) stm = fun addr params locals payable stm ->
 match stm with
  | ReturnRhs _
  | Return
  | Revert -> [],stm
  | Assign(lhs,rhs,cont) ->
     let meths,cont = norm_stm addr params locals payable cont in
     let make_cont () =
       let TaggedVarList(varstags,vars) =
        Parser.tagged_var_list_of_any_var_list
         (Parser.varlist_append (AnyVarList params) (AnyVarList locals)) in
       let Aux(klhs,(lhs_tag,ret_param)) =
        match lhs with
           LVar v -> Aux(Some lhs,(fst v,Var v))
         | LField v -> Aux(Some lhs,(fst v,Var v))
         | LDiscard -> Aux(None,(Int,Value 0)) in
       let varstags = TCons(lhs_tag,varstags) in
       let retparam = lhs_tag,"_ret_" in
       let fparams = VCons(retparam,vars) in
       let sname= Utils.trd3 addr ^ "_" ^ string_of_int (Hashtbl.hash cont) in
       let name = Utils.fst3 addr,varstags,sname in
       let aparams = ECons(ret_param,expr_list_of_var_list vars) in
       let cont =
        Option.fold ~none:cont
         ~some:(fun klhs -> Assign(klhs,Expr(Var(retparam)),cont)) klhs in
       AnyMethodDecl(name,Block(fparams,VNil,cont),payable)::meths,
        Assign(lhs,rhs,ReturnRhs(Call (This,name,None,aparams))) in
     (match lhs,cont with
         LDiscard,Return -> meths,ReturnRhs rhs
       | LVar v,ReturnRhs (Expr (Var v')) ->
          (match eq_tag (fst v) (fst v') with
              Some Refl when snd v = snd v' -> meths,ReturnRhs rhs
            | _ -> make_cont ())
       | _ -> make_cont ())
  | IfThenElse(g,stm1,stm2,cont) ->
     let meths1,stm1 = norm_stm addr params locals payable (stm_concat stm1 cont) in
     let meths2,stm2 = norm_stm addr params locals payable (stm_concat stm2 cont) in
     meths1@meths2,IfThenElse(g,retype_stm stm1,retype_stm stm2,Revert)

let norm_block addr payable (Block(params,locals,stm)) =
 let meths,stm = norm_stm addr params locals payable stm in
 meths,Block(params,locals,stm)

let rec norm_methods =
 function
    [] -> []
  | AnyMethodDecl(name,block,payable)::tl ->
     let meths,block = norm_block name payable block in
     meths @ [AnyMethodDecl(name,block,payable)] @ norm_methods tl

let norm_a_contract (AContract(addr,meths,fallback,fields)) =
 let meths1 = norm_methods meths in
 let meths2,fallback =
  match fallback with
     None -> [],None
   | Some fb ->
      let meths2,fb = norm_block (Unit,TNil,"fallback") true fb in
       meths2,Some fb in
 AContract(addr,meths1@meths2,fallback,fields)

let normalize =
 List.map norm_a_contract
