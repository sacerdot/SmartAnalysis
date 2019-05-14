open SmartCalculus

open ParserCombinator
open Genlex

type any_expr = AnyExpr : 'a tag * 'a expr -> any_expr

(*Utils*)

let fst = (fun x _ -> x)
let scd = (fun _ x -> x)

let addel = (fun l el -> l@[el]) 
let identity = (fun x -> x)

let pp_anytag (AnyTag x) = pp_tag x

let rec print_table table =
    match table with
    | [] -> print_endline
    | ParserCombinator.Field(AnyField(f), _) :: tl -> print_string("var
    ");print_endline (pp_field f); print_table tl
    | Fun(t,_,name) :: tl -> print_string("fun ");print_string (pp_anytag t);
    print_string " "; print_endline name; print_table tl;;

let rec print_token_list l =
    match l with
    | (Kwd x)::l -> print_string "Kwd "; print_string x; print_endline ""; print_token_list l
    | (Ident x)::l -> print_string "Ident "; print_string x; print_endline ""; print_token_list l
    | (Int n)::l -> print_string "int "; print_int n; print_endline ""; print_token_list l
    | (Char c)::l -> print_string "char "; print_char c; print_endline ""; print_token_list l
    | (String s)::l -> print_string "string "; print_string s; print_endline ""; print_token_list l
    | _ -> ()

(*Cast*)
let token_to_string t =
    match t with
    | Kwd x -> x
    | Ident x -> x
    | String x -> x
    | _ -> raise Fail

let token_to_int t = 
    match t with
    | Int x -> x
    | _ -> raise Fail

let token_to_bool t = 
    match t with
    | Kwd "true" -> true
    | Kwd "false" -> false 
    | _ -> raise Fail

let rec remove_minspace =
    function
    | [] -> []
    | (Int x)::tl -> 
            if (x < 0) then [(Kwd "-")]@[(Int (-x))]@(remove_minspace tl) else
                [(Int x)]@(remove_minspace tl)
    | hd::tl -> [hd]@(remove_minspace tl)
(*Expression *)
let plus e1 e2 = Plus(e1,e2)

let minus e = Minus(e)

let subtract e1 e2 = plus e1 (minus e2)

let mult_int c e = match c with Value v -> Mult(Numeric(v),e) | _-> raise Fail

let mult_string c e = match c with Value v -> Mult(Symbolic(v),e) | _-> raise Fail

let max e1 e2 = Max(e1,e2)

let gt e1 e2 = Gt(e1,e2)

let ge e1 e2 = Geq(e1,e2)

let eq tag e1 e2 = Eq(tag,e1,e2)

let lt e1 e2 = gt e2 e1

let le e1 e2 = ge e2 e1

let andb e1 e2 = And(e1,e2)

let orb e1 e2 = Or(e1,e2)

let notb e = Not(e)

let scd_notb _ e = notb e

let neq tag e1 e2 = notb (eq tag e1 e2)

(*Type*)
let int = val_token (fun x -> Value (token_to_int x))

let string = val_token (fun x -> Value (token_to_string x))

let bool = val_token (fun x -> Value (token_to_bool x))

(*Expression*)

let varname s tbl = match s with | (Ident x) :: tl -> (nnext 1 s),x,tbl | _ -> raise Fail

let base tag =
    let var_gr s tbl = let (ns, name, ntbl) = varname s tbl in 
    match (get_vartag ntbl name) with
    | Some AnyTag t ->
            (match (eq_tag t tag) with
            | Some x -> ns,Var(tag,name),ntbl
            | None -> raise Fail)
            | _ -> raise Fail
    in
    choice_list[
        var_gr;
        const (Kwd "fail") (fun _ -> SmartCalculus.Fail);
    ]
(* Int Expression
 * base_int_expr := int | "-" base_int_expr | varname
 * int_expr := base int_expr ("+" int_expr |  "*" int_expr | "-" int_expr) | "max" int_expr int_expr 
 * | "(" int_expr ")"
 *)
let int_expr = 
    (*input è quello che ho già parsato, mentre s è quello che devo ancora parsare*)
   (let rec rec_int_expr input s tbl =
        let int_base =
            choice_list [
                (*Symbol*)
                val_token (fun t -> match t with | String x -> Symbol(x) | _ -> raise Fail);
                int; base Int;] in

        let single_input f ast =
            match input with
            | None -> rec_int_expr (Some (f ast))
            | _ -> raise Fail in

        let double_input f ast =
            match input with
            | Some x -> rec_int_expr (Some (f x ast))
            | _ -> raise Fail in

        let pars_operator pars f s tbl =
            let (ns,nast,ntbl) = pars s tbl in
            single_input f nast ns ntbl in 

        let single_operator tok f =
            pars_operator (concat (const tok ignore)
            (rec_int_expr None) scd) f in 


        let double_operator tok f s tbl =
            let (ns,nast,ntbl) = (concat (const tok ignore)
            (rec_int_expr None) scd) s tbl in 
            double_input f nast ns ntbl in

        (try
            choice_list [ 
                (*mult int*)
                pars_operator 
                (concat int (concat (const (Kwd "*") ignore) 
                (rec_int_expr None) scd) mult_int) identity; 
                (*mult string*)
                pars_operator (concat string (concat (const (Kwd "*") ignore) 
                (rec_int_expr None) scd) mult_string) identity;
                (*base*)
                pars_operator int_base identity;
                (*plus*)
                double_operator (Kwd "+") plus;
                (*minus*)
                double_operator (Kwd "-") subtract;
                (*single minus*)
                single_operator (Kwd "-") minus;
                (*max*)
                pars_operator 
                (concat (const (Kwd "max") ignore)
                (concat (concat (const (Kwd "(") ignore) (concat (rec_int_expr None)
                (const (Kwd ",") ignore) fst) scd) (concat (rec_int_expr None)
                (const (Kwd ")") ignore) fst) max ) scd) identity;
                (*brackets*)
                pars_operator 
                (concat (concat (const (Kwd "(") ignore) (rec_int_expr
                    None) scd) (const (Kwd ")") ignore) fst) identity; 
            ] s tbl
            with Fail -> (match input with
            | None -> raise Fail
            | Some x -> (s,x,tbl)))
        in rec_int_expr None)

let str_expr = (choice (base String) string)

        
let bool_expr = 
        (*input è quello che ho già parsato, mentre s è quello che devo ancora parsare*)
        let rec rec_bool_expr input s tbl =
            let bool_base =
                choice_list[
                    bool;
                    base Bool;
                    (*Greater*)
                    concat 
                    int_expr (concat (const (Kwd ">") ignore) int_expr scd) gt;
                    (*Greater or Equal*)
                    concat 
                        int_expr (concat (const (Kwd ">=") ignore) int_expr scd) ge;
                    (*Equal*)
                    concat 
                        int_expr (concat (const (Kwd "==") ignore) int_expr scd) (eq Int);
                    concat 
                        str_expr (concat (const (Kwd "==") ignore) str_expr scd) (eq String);
                    (*Not equal*)
                    concat 
                        int_expr (concat (const (Kwd "!=") ignore) int_expr scd) (neq Int);
                    concat 
                        str_expr (concat (const (Kwd "!=") ignore) str_expr scd) (neq String);
                    (*Lesser*)
                    concat 
                        int_expr (concat (const (Kwd "<") ignore) int_expr scd) lt;
                    (*Greater or Equal*)
                    concat 
                        int_expr (concat (const (Kwd "<=") ignore) int_expr scd) le;
                ] in

            let single_input f ast =
                match input with
                | None -> rec_bool_expr (Some (f ast))
                | _ -> raise Fail in

            let double_input f ast =
                match input with
                | Some x -> rec_bool_expr (Some (f x ast))
                | _ -> raise Fail in

            let pars_operator pars f s tbl =
                let (ns,nast,ntbl) = pars s tbl in
                single_input f nast ns ntbl in 

            let single_operator tok f =
                pars_operator (concat (const tok ignore)
                (rec_bool_expr None) scd) f in 

            let double_operator tok f s tbl =
                let (ns,nast,ntbl) = (concat (const tok ignore)
                (rec_bool_expr None) scd) s tbl in 
                double_input f nast ns ntbl in

            try (
                choice_list [
                    (*Base*)    
                    pars_operator bool_base identity;
            (*And*)
            double_operator (Kwd "&&") andb;
            (*Or*)
            double_operator (Kwd "||") orb;
            (*Eq*)
            double_operator (Kwd "==") (eq Bool);
            (*Neq*)
            double_operator (Kwd "!=") (neq Bool);
            (*Not*)
            single_operator (Kwd "!") notb;
            (*Brackets*)
            pars_operator (concat (concat (const (Kwd "(") ignore)
            (rec_bool_expr None) scd) (const (Kwd ")") ignore) fst) identity; 
            ] s tbl)
            with Fail -> 
                (match input with
                | None -> raise Fail
                | Some x -> (s,x,tbl))
        in rec_bool_expr None


let expr_gr (AnyTag tag) s tbl =
    let pars p = (let (s1, ast1, tbl1) = p s tbl in s1,(AnyExpr(tag,ast1)),tbl1) in
    match tag with
    | Int -> pars int_expr
    | Bool -> pars bool_expr
    | ContractAddress -> pars (choice (base ContractAddress) (const (Kwd "this")
    (fun _ -> This)))
    | String -> pars str_expr
    | x -> pars (base x)

let any_expr_gr = choice_list[
    expr_gr (AnyTag Int);
    expr_gr (AnyTag Bool);
    expr_gr (AnyTag String);
    expr_gr (AnyTag ContractAddress);
    expr_gr (AnyTag HumanAddress);
    ]

(*Method call*)

let get_table_field s tbl =
    let (ns, fname, ntbl) = varname s tbl in 
    match get_vartag ntbl fname with
    | Some (AnyTag x) -> ns,(AnyField(x, fname)),ntbl
    | _ -> raise Fail

let get_table_fun s tbl =
    let (ns, fname, ntbl) = varname s tbl in 
    match get_funtag ntbl fname with
    | Some x -> fname,x
    | _ -> raise Fail


let call_gr tag s tbl =
    let rec prmt l s tbl = 
        match l with 
        | [] -> s,[],tbl
        | x::[] -> let (s1,ast1,tbl1) = expr_gr x s tbl in (s1,[ast1],tbl1)
        | x::tl -> concat (concat (expr_gr x) (const (Kwd ",") ignore)
        fst) (prmt tl) (fun x y -> addel y x) s tbl in
    (*Risolve i parametri tra parentesi es.(4,3,true) con controllo sui tipi*)
    let brackets l = concat (concat (const (Kwd "(") ignore) (prmt l) scd) 
    (const (Kwd ")") ignore) fst in

    let (ns1, funname, ntbl1) = varname s tbl in 
        match get_funtag ntbl1 funname with
        | Some((AnyTag x),tagl) -> (
            match eq_tag tag x with
            | Some _ -> (let (ns2, elist, ntbl2) = brackets tagl ns1 ntbl1 in
                let rec aux acc l =
                    match acc,l with
                    | _,[] -> acc
                    | Call(opt,(tg,tgl,name),expl),(AnyExpr (t,expr))::tl -> aux
                    (Call(opt,(tg,TCons(t,tgl),name),ECons(expr,expl))) tl
                    | _,_ -> raise Fail
                in (ns2, AnyRhs(tag,(aux (Call(None,(tag,TNil,funname),ENil)) (List.rev
                elist))), ntbl2))
            | None -> raise Fail)
        | None -> raise Fail

let rhs_gr (AnyTag tag) = 
    choice (fun s tbl -> let (ns, expr, nt) = expr_gr (AnyTag tag) s tbl in 
        match expr with 
        | AnyExpr(t,e) -> ns,(AnyRhs(t,(Expr e))),nt)
    (call_gr tag)

let any_rhs_gr = choice_list[
    rhs_gr (AnyTag Int);
    rhs_gr (AnyTag Bool);
    rhs_gr (AnyTag String);
    rhs_gr (AnyTag ContractAddress);
    rhs_gr (AnyTag HumanAddress);
    ]

(*Store*)
let type_gr = choice_list[
        const (Kwd "int") (fun _ -> AnyTag(Int));
        const (Kwd "string")  (fun _ -> AnyTag(String));
        const (Kwd "bool") (fun _ -> AnyTag (Bool));
        const (Kwd "Contract") (fun _ -> AnyTag (ContractAddress));
        const (Kwd "Human") (fun _ -> AnyTag (HumanAddress));
] 

let field_gr = concat type_gr varname (fun at v -> match at with | AnyTag t -> AnyField (t,v)) 

let add_table_field funname s tbl = 
    let (t ,ast, ntbl) = field_gr s tbl in 
        match ast with 
        | (AnyField (x,v)) -> t,ast,(add_field_to_table ntbl x v funname)
                    
let declare_gr s tbl = 
    (let (tok, ast, ntbl) = concat (add_table_field "main") (const (Kwd "=") ignore) fst s tbl in
    (*Prende un field e lo mette col suo value*)
    match ast with
        | (AnyField (tag, name)) ->
                let aux tg f = let (vtok, vast, vntbl) = val_token f tok ntbl in vtok,Let((tg,name),vast),vntbl in
                    match tag with
                    | SmartCalculus.Int ->  aux Int token_to_int
                    | SmartCalculus.String -> aux String token_to_string
                    | SmartCalculus.Bool -> aux Bool token_to_bool
                    | _ -> raise Fail) 

let store_gr s tbl = kleenestar declare_gr [] addel s tbl

(*Methods def*)
let meth_gr s tbl = 
    let parameters_gr pars = 
        concat (concat (const (Kwd "(") ignore) (option
        (concat (kleenestar (concat pars (const (Kwd ",") ignore) fst) [] addel)
        pars addel)) scd) (const (Kwd ")") ignore) fst in
    let rec get_taglist l = match l with [] -> [] | AnyField(t, _)::tl ->
        [AnyTag t]@(get_taglist tl) in
    let (ns1, AnyField(funtag, funname), ntbl1) = field_gr s tbl in 
    let (ns2, flist, ntbl2) = (parameters_gr (add_table_field funname) ns1 ntbl1) in
    let delopt l = match l with | Some x -> x| None -> [] in
    ns2,(AnyField(funtag,funname),flist),(add_fun_to_table ntbl2 funtag (get_taglist (delopt flist)) funname)

(*Statements*)
let assign_var_gr s tbl = 
    let (ns1, field, nt1) = concat get_table_field (const (Kwd "=") ignore) fst s tbl in
    match field with 
    | AnyField (ft,nfield) -> 
            let (ns2, anyrhs, nt2) = rhs_gr (AnyTag ft) ns1 nt1 in
            match anyrhs with
    | AnyRhs (rt, rhs) -> (ns2, (Assign((rt,nfield),rhs)),nt2)

let rec list_to_comp l =
    match l with
    | x :: [] -> x
    | hd :: tl -> Comp(hd, (list_to_comp tl))
    | [] -> raise Fail

let rec stm_gr tag s tbl =
    choice_list[
        (*assign*)
        assign_var_gr;

        (*if then else*)
        concat (concat (concat (concat (const (Kwd "if") ignore) bool_expr
        scd)(const (Kwd "then") ignore) fst ) (stm_gr tag)(fun x y -> x,y))
        (concat(const (Kwd "else") ignore) (stm_gr tag) scd) 
        (fun (bexp,stm1) stm2 -> IfThenElse(bexp,stm1,stm2));

        (*{Comp}*)
        concat(concat (const (Kwd "{") ignore) (kleenestar (stm_gr tag) []
        addel)(fun _ l -> list_to_comp l)) (const (Kwd "}") ignore) fst;

        (*Choice*)
        (match tag with
            | AnyTag HumanAddress ->
                concat (concat (const (Kwd "choice") ignore) (stm_gr tag)
                scd)(stm_gr tag) (fun x y -> Choice(x,y))
            | _ -> raise Fail)] s tbl


let stm_list_gr tag = kleenestar (stm_gr tag) [] addel

let anymeth_gr tag s tbl =
    let (s1,(((AnyField(funtag,funname)),parlopt),stm),tbl1) = 
        concat meth_gr (stm_list_gr tag) (fun x y -> x,y) s tbl in
    let (s2,(AnyExpr(outtag,retexpr)),tbl2) = 
        concat (const (Kwd "return") ignore) (expr_gr (AnyTag funtag)) scd
        s1 tbl1 in
    let par_list opt =
        match opt with
        | None -> []
        | Some x -> x in
    let rec aux acc tag_list =
        match acc,tag_list with
        | _,[] -> acc
        |(AnyMethodDecl((tag,tag_list,funct),(var_list,s,expr))),((AnyField(tf,name))::tl)
        -> aux (AnyMethodDecl((tag,(TCons(tf,tag_list)),funct),((VCons((tf,name),var_list)),s,expr))) tl
    
    in s2,(aux (AnyMethodDecl((outtag,TNil,funname),(VNil,stm,retexpr)))(par_list parlopt)),(remove_local_var tbl2 funname)

let methods_gr tag = kleenestar (anymeth_gr tag) [] addel

let address_gr (AnyTag tag) s tbl =
    let (ns, AnyField(t, name), nt) = add_table_field "main" s tbl in 
    match tag,t with
    | ContractAddress,ContractAddress -> (ns,(AnyAddress(Contract name)),nt)
    | HumanAddress,HumanAddress -> (ns,(AnyAddress(Human name)),nt)
    | _,_ -> raise Fail


let contract_gr s tbl =
    let (ns1,(AnyAddress contract),ntbl1) = address_gr (AnyTag
    ContractAddress) s tbl in
    let (ns2,store,ntbl2) = store_gr ns1 ntbl1 in
    let (ns3,methods,ntbl3) = methods_gr (AnyTag ContractAddress) ns2 ntbl2 in
        match contract with 
        | Contract name -> ns3,((Contract name),methods,store),ntbl3
        | _ -> raise Fail

let human_gr s tbl =
    let (ns1,(AnyAddress human),ntbl1) = address_gr (AnyTag
    HumanAddress) s tbl in
    let (ns2,store,ntbl2) = store_gr ns1 ntbl1 in
    let (ns3,methods,ntbl3) = methods_gr (AnyTag HumanAddress) ns2 ntbl2 in
    let (ns4,stack,ntbl4) = concat (const (Kwd "return") ignore) any_rhs_gr
    scd ns3 ntbl3 in
        match human with 
        | Human name -> ns4,((Human name),methods,store,stack),ntbl4
        | _ -> raise Fail



(*testing*)
let in_channel = open_in "input"
let file = Stream.of_channel(in_channel)
let lexer = make_lexer["+"; "-"; "*"; "max"; "("; ")"; ">"; ">="; "=="; "<";
"<="; "!="; "&&"; "||"; "!"; "true"; "false"; "int"; "string"; "bool"; "=";
","; "fail"; "if"; "then"; "else"; "{"; "}";"choice";"return";"Human";"Contract"]
let tokens = remove_minspace (of_token(lexer file))
(*print_token_list tokens;;*)
let empty_tbl = []
let (s, l, tbl) = human_gr tokens empty_tbl;;
print_table tbl;;
