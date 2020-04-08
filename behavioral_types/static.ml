open MicroSolidity

(** Normalization **)

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

(** Stack length bounds **)

type bounds = ((address * any_method_decl) * int option) list

exception Unbounded of (address * any_method_decl) list

let get_bound ~f m tbl =
 match List.assoc_opt m tbl with  
    None ->
     let tbl,b = f m ((m,None)::tbl) in
     let tbl = List.remove_assoc m tbl in
     (m,Some b)::tbl,b
  | Some None ->
     let cycle =
      List.filter_map (fun (qid,o) -> if o = None then Some qid else None) tbl
     in
      raise (Unbounded cycle)
  | Some (Some b) -> tbl,b

let get_bounds_rhs ~f ~cfg this rhs tbl =
 match rhs with
 | Expr _ -> tbl,0
 | Call(aexpr,meth,value,_) ->
    let payable = value <> None in
    let methods = match_methods ~this aexpr meth payable cfg in
Utils.error(pp_meth meth ^ " ==> " ^ string_of_int (List.length methods));
    List.fold_left
     (fun (tbl,b) mdecl ->
       let tbl,b1 = get_bound ~f mdecl tbl in tbl,max b b1)
     (tbl,0) methods

let rec get_bounds_stm : type a b. f:'c -> cfg:'d -> address -> (a,b) stm -> bounds -> bounds * int = fun ~f ~cfg addr stm tbl ->
 match stm with
  | ReturnRhs rhs -> get_bounds_rhs ~f ~cfg addr rhs tbl
  | Return
  | Revert -> tbl,0
  | Assign(_,Expr _,stm) ->
     get_bounds_stm ~f ~cfg addr stm tbl
  | Assign(_,rhs1,ReturnRhs rhs2) ->
     let tbl,b1 = get_bounds_rhs ~f ~cfg addr rhs1 tbl in
     let tbl,b2 = get_bounds_rhs ~f ~cfg addr rhs2 tbl in
     tbl, max (1+b1) b2
  | IfThenElse(_,stm1,stm2,Revert) ->
     let tbl,b1 = get_bounds_stm ~f ~cfg addr stm1 tbl in
     let tbl,b2 = get_bounds_stm ~f ~cfg addr stm2 tbl in
     tbl, max b1 b2
  | _ -> assert false

let get_bounds_block ~f ~cfg addr (Block(_,_,stm)) tbl =
 get_bounds_stm ~f ~cfg addr stm tbl

let get_bounds_any_method_decl ~cfg addr tbl m =
 let rec f (addr,AnyMethodDecl(_,b,_)) tbl =
  get_bounds_block ~f ~cfg addr b tbl in
 fst (get_bound ~f (addr,m) tbl)

let get_bounds_a_contract ~cfg tbl (AContract(addr,methods,fallback,_)) =
 List.fold_left (get_bounds_any_method_decl ~cfg addr) tbl
  (match fallback with
      None -> methods
    | Some fb -> any_method_decl_of_fallback fb :: methods)

let get_bounds cfg =
 let l = List.fold_left (get_bounds_a_contract ~cfg) [] cfg in
 List.map (function (m,Some b) -> m,b | _ -> assert false) l

let pp_bounds =
 List.fold_left
  (fun acc ((a,AnyMethodDecl(m,_,_)),b) ->
    acc ^ "\n" ^
     pp_address a ^ "." ^ pp_meth m ^ ": " ^ string_of_int b)
  ""
