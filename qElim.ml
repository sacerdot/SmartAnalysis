type var = string

type var_map = (string * int) list

type expr =
 | Var of var
 | Value of int
 | Plus of expr * expr
 | Mult of int * expr
 | Minus of expr * expr
 (*| Max of expr * expr*)

let smart_mult (k,e) =
 match k with
    0 -> Value 0
  | 1 -> e
  | _ -> Mult(k,e)

let succ =
 function
    Value n -> Value (n+1)
  | e -> Plus(Value 1, e)

type prop =
 [ `Forall of var * prop
 | `Exists of var * prop
 | `Impl of prop * prop
 | `And of prop * prop
 | `Or of prop * prop
 | `Not of prop
 | `Eq of expr * expr
 | `Geq of expr * expr
 | `Gt of expr * expr
 | `Observe of (*negated*)bool * expr option * prop list ]

type dnf_atom =
 [ `Geq of expr * expr
 | `Observe of (*negated*)bool * expr option * prop list ]

type dnf = dnf_atom list list

(**** Pretty printing ****)
let rec pp_expr =
 function
 | Var v -> v
 | Value n -> string_of_int n
 | Plus(e1,e2) -> "(" ^ pp_expr e1 ^ " + " ^ pp_expr e2 ^ ")"
 | Mult(k,e) -> string_of_int k ^ " * " ^ pp_expr e
 | Minus(e1,e2) -> "(" ^ pp_expr e1 ^ " - " ^ pp_expr e2 ^ ")"

let rec pp_prop =
 function
 | `Forall(v,p) -> "!" ^ v ^ "." ^ pp_prop p
 | `Exists(v,p) -> "?" ^ v ^ "." ^ pp_prop p
 | `Impl(p1,p2) -> "(" ^ pp_prop p1 ^ " => " ^ pp_prop p2 ^ ")"
 | `And(p1,p2) -> "(" ^ pp_prop p1 ^ " /\\ " ^ pp_prop p2 ^ ")"
 | `Or(p1,p2) -> "(" ^ pp_prop p1 ^ " \\/ " ^ pp_prop p2 ^ ")"
 | `Not p -> "-" ^ pp_prop p
 | `Eq(e1,e2) -> pp_expr e1 ^ " = " ^ pp_expr e2
 | `Geq(e1,e2) -> pp_expr e1 ^ " >= " ^ pp_expr e2
 | `Gt(e1,e2) -> pp_expr e1 ^ " > " ^ pp_expr e2
 | `Observe(b,e,pl) ->
     "[" ^ string_of_bool b ^ "," ^
       (match e with None -> "_" | Some e -> pp_expr e) ^ "," ^
       String.concat " /\\ " (List.map pp_prop pl) ^ "]"

let pp_dnf (orl : dnf) =
 String.concat " \\/ "
  (List.map
    (fun andl ->
      if andl = [] then "TRUE" else
      String.concat " /\\ "
       (List.map (fun e -> pp_prop (e : dnf_atom :> prop)) andl))
    orl)

(*** quantifier elimination ***)

let one = "1"

let rec negate : prop -> _ =
 function
 | `Forall(v,p) -> `Exists(v,negate p)
 | `Exists(v,p) -> `Forall(v,negate p)
 | `Impl(p1,p2) -> `And(p1,negate p2)
 | `And(p1,p2) -> `Or(negate p1, negate p2)
 | `Or(p1,p2) -> `And(negate p1, negate p2)
 | `Not p -> p
 | `Eq(e1,e2) -> `Or(`Geq(e1,succ e2),`Geq(e2,succ e1))
 | `Geq(e1,e2) -> `Geq(e2,succ e1)
 | `Gt(e1,e2) -> `Geq(e2,e1) 
 | `Observe(b,e,cs) -> `Observe(not b,e,cs)

let and_dnf (p1 : dnf) (p2 : dnf) : dnf =
 List.fold_left
  (fun res andl1 ->
    List.map
     (fun andl2 ->
       andl1 @ andl2
     ) p2 @ res
  ) [] p1

let or_dnf (p1 : dnf) (p2 : dnf) : dnf = p1 @ p2

let rec dnf_of_atom : _ -> dnf =
 function
 | `Eq(e1,e2) -> [[`Geq(e1,e2);`Geq(e2,e1)]]
 | `Gt(e1,e2) -> [[`Geq(e1,succ e2)]]
 | `Geq _
 | `Observe _ as p -> [[p]]

let prop_of_ands (ands : dnf_atom list) : prop option =
 if ands = [] then None else
  let rec aux =
   function
      [] -> assert false
    | [p] -> (p : dnf_atom :> prop)
    | p::ps -> `And((p : dnf_atom :> prop), aux ps)
  in Some (aux ands)

let rec prop_of_dnf : dnf -> prop =
 function
    [] -> `Geq(Value 0, Value 1)
  | [p] ->
     (match prop_of_ands p with
         None -> `Geq(Value 0, Value 0)
       | Some p -> p)
  | p::ps ->
     match prop_of_ands p with
        None -> `Or(`Geq(Value 0, Value 0),prop_of_dnf ps)
      | Some p -> `Or(p,prop_of_dnf ps)

let mult n l =
 if n = 0 then [] else List.map (fun (v,k) -> v,k*n) l

let rec combine op l1 l2 =
 match l1,l2 with
    [],l -> List.map (fun (v,k) -> v, op 0 k) l
  | l,[] -> l
  | x1::xs1,x2::xs2 when fst x1 = fst x2 ->
     let res = op (snd x1) (snd x2) in
     if res = 0 then combine op xs1 xs2
     else (fst x1,res)::combine op xs1 xs2
  | x1::xs1,x2::_ when fst x1 < fst x2 ->
     (fst x1,op (snd x1) 0)::combine op xs1 l2
  | _,x2::xs2 ->
     (fst x2,op 0 (snd x2))::combine op l1 xs2

let rec eval : expr -> (var * int) list =
 function
  | Var v -> [v,1]
  | Value v -> if v = 0 then [] else [one,v]
  | Plus(e1,e2) -> combine (+) (eval e1) (eval e2)
  | Mult(n,e) -> mult n (eval e)
  | Minus(e1,e2) -> combine (-) (eval e1) (eval e2)
  (*| Max(e1,e2) ->*)

let simplify (e1,e2) =
 combine (-) (eval e1) (eval e2)

let rec gcd u v =
  if v <> 0 then (gcd v (u mod v))
  else (abs u)
 
let lcm m n =
  match m, n with
  | 0, _ | _, 0 -> 0
  | m, n -> abs (m * n) / (gcd m n)

let rec big_lcm v =
 function
    [] -> 1
  | vl::vls ->
     let n = try List.assoc v vl with Not_found -> 1 in
      lcm n (big_lcm v vls)

let rec scale lcm v =
 function
    [] -> [],[],[]
  | eq::eql ->
     let leql,geql,otherl = scale lcm v eql in
     try
      let k = List.assoc v eq in
      assert(k <> 0);
      let eq =
       Lib.map_skip
        (fun (v',k') ->
          if v = v' then None else Some (v',k'*abs(lcm/k))
        ) eq in
      if k < 0 then
       eq::leql,geql,otherl
      else
       leql,eq::geql,otherl
     with
      Not_found -> leql,geql,eq::otherl

let rec expr_of_var_map : _ -> expr option =
 function
    [] -> None
  | map ->
     let rec aux =
      function
         [] -> assert false
       | [v,k] when v = one -> Value k
       | [v,k] -> smart_mult(k,Var v)
       | (v,k)::map when v = one -> Plus(Value k, aux map)
       | (v,k)::map -> Plus(smart_mult(k,Var v), aux map)
     in Some (aux map)

exception Skip

let elim_andl v (andl : dnf_atom list) : dnf_atom list option =
 let obs =
  Lib.map_skip
   (function
       `Observe(b,e,cs) -> Some (b,e,cs)
     | _ -> None) andl in
 let obs = if obs = [] then [false,None,[]] else obs in
(*prerr_endline ("BEFORE: " ^ String.concat " , " (List.map (fun e -> pp_prop (e : dnf_atom :> prop)) andl));*)
 let eql =
  Lib.map_skip
   (function `Geq(e1,e2) -> Some (e1,e2) | _ -> None) andl in
 let eql = List.map simplify eql in
(*prerr_endline ("AFTER: " ^ String.concat " , " (List.map (fun l -> match expr_of_var_map l with None -> "#" | Some e -> pp_expr e) eql));*)
 let lcm = big_lcm v eql in
 let leql,geql,otherl = scale lcm v eql in
(*prerr_endline ("## " ^ string_of_int (List.length leql) ^ " !! " ^ string_of_int (List.length geql));*)
 let obs =
  List.map
   (function (b,e,cs) ->
     let leql = Lib.map_skip expr_of_var_map leql in
     let geql = List.map (List.map (fun (v,k) -> v, -k)) geql in
     let geql = Lib.map_skip expr_of_var_map geql in
     let leql =
      List.map (fun e -> `Geq(e,smart_mult(lcm,Var v))) leql in
(*prerr_endline ("!leql! " ^ String.concat " , " (List.map (fun e -> pp_prop (e : dnf_atom :> prop)) leql));*)
     let geql =
      List.map (fun e -> `Geq(smart_mult(lcm,Var v),e)) geql in
(*prerr_endline ("!geql! " ^ String.concat " , " (List.map (fun e -> pp_prop (e : dnf_atom :> prop)) geql));*)
     `Observe(b,e,cs@leql@geql)
   ) obs in
 try
 let geq_min_max =
  List.fold_left
   (fun res leq ->
     List.fold_left
      (fun res geq ->
        let diff = combine (-) leq geq in
        (match expr_of_var_map diff with
           None -> None
         | Some diff ->
            (match diff with
                Value k when k < 0 -> raise Skip
              | Value k when k >= 0 -> None
              | _ -> Some (`Geq(diff,Value 0))))::res
      ) res geql
   ) [] leql in
 let geq_min_max = Lib.map_skip (fun x -> x) geq_min_max in
 let otherl =
  Lib.map_skip
   (fun map ->
     Lib.map_option (fun e -> `Geq(e,Value 0))
      (expr_of_var_map map)
   ) otherl in
 Some (geq_min_max @ otherl @ obs)
 with Skip -> None

let rec elim v =
 function
    [] -> []
  | andl::andls ->
     match elim_andl v andl with
        None -> elim v andls
      | Some andl -> andl :: elim v andls

let rec qe : prop -> dnf =
 function
xxx ->
let res = match xxx with
 | `Forall(v,p) -> qe (`Not(prop_of_dnf (qe(`Exists(v,`Not p)))))
 | `Exists(v,p) -> elim v (qe p)
 | `Impl(p1,p2) -> qe (`Or(`Not p1, p2))
 | `And(p1,p2) -> and_dnf (qe p1) (qe p2)
 | `Or(p1,p2) -> or_dnf (qe p1) (qe p2)
 | `Not p -> qe (negate p)
 | `Eq _
 | `Geq _
 | `Gt _
 | `Observe _ as p -> dnf_of_atom p
in
prerr_endline ("QE: " ^ pp_prop xxx ^ "\n ==>\n" ^ pp_dnf res ^ "\n");
res

(*** test ***)

let x = Var "x"
let y = Var "y"

let test1 : prop =
 `Forall("x",`Impl(`And(`Geq(x,Value 1),`Geq(Value 4,x)),
 `Exists("y",`Or(`Or(
   `And(`Gt(x,y),`Eq(Value 0,Value 0)),
   `And(`And(`Geq(y,x),`Gt(Mult(2,x),y)),`Observe(false,Some(Plus(x,Mult(2,y))),[]))),
   `And(`Geq(y,Mult(2,x)),`Observe(false,Some(Plus(Mult(2,x),y)),[]))))))

let res1 = qe test1

let _ =
 prerr_endline (pp_prop test1 ^ "\n ===>\n" ^ pp_dnf res1)
