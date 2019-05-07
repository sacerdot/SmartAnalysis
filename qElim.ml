type var = string

let one = "1"

type var_map = (string * int) list

type expr =
 | Var of var
 | Value of int
 | Plus of expr * expr
 | Mult of int * expr
 | Minus of expr * expr
 (*| Max of expr * expr*)

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
 | `Leq of expr * expr
 | `Lt of expr * expr
 | `Observe of (*negated*)bool * expr ]

type cstr = [ `Leq of var_map ]

type dnf_atom =
 [ cstr
 | `Observe of (*negated*)bool * expr option * cstr list ]

type dnf = dnf_atom list list

(**** Pretty printing ****)
let rec pp_expr =
 function
 | Var v -> v
 | Value n -> string_of_int n
 | Plus(e1,e2) -> "(" ^ pp_expr e1 ^ " + " ^ pp_expr e2 ^ ")"
 | Mult(k,e) -> string_of_int k ^ " * " ^ pp_expr e
 | Minus(e1,e2) -> "(" ^ pp_expr e1 ^ " - " ^ pp_expr e2 ^ ")"

let rec pp_prop : prop -> string =
 function
 | `Forall(v,p) -> "!" ^ v ^ "." ^ pp_prop p
 | `Exists(v,p) -> "?" ^ v ^ "." ^ pp_prop p
 | `Impl(p1,p2) -> "(" ^ pp_prop p1 ^ " => " ^ pp_prop p2 ^ ")"
 | `And(p1,p2) -> "(" ^ pp_prop p1 ^ " /\\ " ^ pp_prop p2 ^ ")"
 | `Or(p1,p2) -> "(" ^ pp_prop p1 ^ " \\/ " ^ pp_prop p2 ^ ")"
 | `Not p -> "-" ^ pp_prop p
 | `Eq(e1,e2) -> pp_expr e1 ^ " = " ^ pp_expr e2
 | `Leq(e1,e2) -> pp_expr e1 ^ " <= " ^ pp_expr e2
 | `Lt(e1,e2) -> pp_expr e1 ^ " < " ^ pp_expr e2
 | `Observe(b,e) ->
     "[" ^ string_of_bool b ^ "," ^ pp_expr e ^ "]"

let rec pp_var_map ?(first=true) =
 function
    [] -> if first then "0" else ""
  | (v,k)::tl ->
     let k = if first then k else abs k in
     (if v = one then string_of_int k
      else
        (if k = 1 then "" else if k = -1 then "-" else string_of_int k ^ "*")
        ^ v) ^
     (match tl with [] -> "" | (_,k)::_ -> if k > 0 then " + " else " - ") ^
     pp_var_map ~first:false tl

let rec pp_dnf_atom : dnf_atom -> string =
 function
    `Leq vm -> pp_var_map vm ^ " <= 0"
  | `Observe(b,e,cstrs) ->
     "[" ^ string_of_bool b ^ "," ^
      (match e with None -> "_" | Some e -> pp_expr e) ^ "," ^
      String.concat ","
       (List.map (fun c -> pp_dnf_atom (c : cstr :> dnf_atom)) cstrs) ^ "]"

let pp_dnf (orl : dnf) =
 if orl = [] then "FALSE" else "   " ^
  String.concat "\n\\/ "
   (List.map
    (fun andl ->
      if andl = [] then "TRUE" else
      String.concat " /\\ "
       (List.map pp_dnf_atom andl))
    orl)

(*** quantifier elimination ***)

let combine op l1 l2 =
 let rec aux l1 l2 =
  match l1,l2 with
    [],l -> List.map (fun (v,k) -> v, op 0 k) l
  | l,[] -> l
  | x1::xs1,x2::xs2 when fst x1 = fst x2 ->
     (fst x1,op (snd x1) (snd x2))::aux xs1 xs2
  | x1::xs1,x2::_ when fst x1 < fst x2 ->
     (fst x1,op (snd x1) 0)::aux xs1 l2
  | _,x2::xs2 ->
     (fst x2,op 0 (snd x2))::aux l1 xs2
 in
  Lib.map_skip (function (_,0) -> None | x -> Some x) (aux l1 l2)

let plus = combine (+)
let minus = combine (-)

let mult n (l : var_map) : var_map =
 if n = 0 then [] else List.map (fun (v,k) -> v,k*n) l

let rec var_map_of_expr : expr -> var_map =
 function
  | Var v -> [v,1]
  | Value v -> if v = 0 then [] else [one,v]
  | Plus(e1,e2) -> plus (var_map_of_expr e1) (var_map_of_expr e2)
  | Mult(n,e) -> mult n (var_map_of_expr e)
  | Minus(e1,e2) -> minus (var_map_of_expr e1) (var_map_of_expr e2)
  (*| Max(e1,e2) ->*)

let true_dnf = [[]]
let false_dnf = []

let and_dnf p1 p2 =
 List.fold_left
  (fun res andl1 ->
    List.map
     (fun andl2 ->
       andl1 @ andl2
     ) p2 @ res
  ) [] p1

let or_dnf (p1 : dnf) (p2 : dnf) : dnf = p1 @ p2

let and_dnfl l = List.fold_left (fun res x -> and_dnf res x) true_dnf l
let or_dnfl = List.fold_left (fun res x -> or_dnf res x) false_dnf

let negate_var_map (m : var_map) : var_map = plus (mult (-1) m) [one,1]

let dnf_of_var_map m =
 match m with
    [] -> true_dnf
  | [v,k] when v = one -> if k < 0 then true_dnf else false_dnf
  | _ -> [[`Leq m]]

let negate_dnf_atom =
 function
    `Leq m -> dnf_of_var_map (negate_var_map m)
  | `Observe(b,e,l) -> [[`Observe(not b,e,l)]]

let rec not_dnf : dnf -> dnf =
 function
    [] -> true_dnf
  | p::ps ->
     let ps = not_dnf ps in
     List.fold_left (fun res x ->
      List.fold_left (fun res xs ->
       or_dnf (and_dnf (negate_dnf_atom x) [xs]) res) res ps
      ) false_dnf p
;;

let eval_leq e1 e2 =
 dnf_of_var_map (minus (var_map_of_expr e1) (var_map_of_expr e2))

let rec dnf_of_atom : _ -> dnf =
 function
 | `Eq(e1,e2) -> and_dnf (eval_leq e1 e2) (eval_leq e2 e1)
 | `Lt(e1,e2) -> eval_leq (succ e1) e2
 | `Leq(e1,e2) -> eval_leq e1 e2
 | `Observe(b,e) -> [[`Observe(b,Some e,[])]]

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

let elim_andl v (andl : dnf_atom list) : dnf =
 let obs,eql =
  Lib.classify
   (function
       `Observe(b,e,cs) -> `True (b,e,cs)
     | `Leq e -> `False e) andl in
 let obs = if obs = [] then [false,None,[]] else obs in
 let lcm = big_lcm v eql in
 let leql,geql,otherl = scale lcm v eql in
 let otherl = and_dnfl (List.map dnf_of_var_map otherl) in
 let obs =
  List.map
   (function (b,e,cs) ->
     let l =
      and_dnfl
       (List.map (fun e -> dnf_of_var_map (plus [v,-(abs lcm)] e)) leql
       @List.map (fun e -> dnf_of_var_map (plus [v,abs lcm] e)) geql) in
     match l with
        [] -> false_dnf
      | [l] -> [[(`Observe(b,e,cs@l) : dnf_atom)]]
      | _ -> assert false
   ) obs in
 let geq_min_max =
  List.fold_left (fun res leq ->
   List.fold_left (fun res geq ->
    and_dnf (dnf_of_var_map (plus leq geq)) res) res geql
   ) true_dnf leql in
 and_dnfl (geq_min_max::otherl::obs)

let elim v orl = or_dnfl (List.map (elim_andl v) orl)

let rec qe : prop -> dnf =
 function
xxx ->
let res = match xxx with
 | `Forall(v,p) ->
     let np = not_dnf (qe p) in
prerr_endline ("NEGATE:\n" ^ pp_dnf np ^ "\n");
     let en = elim v np in
prerr_endline ("ELIM:\n" ^ pp_dnf en ^ "\n");
     not_dnf en
 | `Exists(v,p) -> elim v (qe p)
 | `Impl(p1,p2) -> or_dnf (not_dnf (qe p1)) (qe p2)
 | `And(p1,p2) -> and_dnf (qe p1) (qe p2)
 | `Or(p1,p2) -> or_dnf (qe p1) (qe p2)
 | `Not p -> not_dnf (qe p)
 | `Eq _
 | `Leq _
 | `Lt _
 | `Observe _ as p -> dnf_of_atom p
in
(*
let res =
 List.map
  (fun andl ->
   if List.exists (function `Observe _ -> true | _ -> false) andl then andl
   else `Observe(false,None,[])::andl
  ) res
in
*)
prerr_endline ("QE: " ^ pp_prop xxx ^ "\n ==>\n" ^ pp_dnf res ^ "\n");
res

(*** test ***)

let x = Var "x"
let y = Var "y"

let test1 : prop =
 `Forall("x",`Impl(`And(`Leq(Value 1,x),`Leq(x,Value 4)),
 `Exists("y",`Or(`Or(
   `Lt(y,x),
   `And(`And(`Leq(x,y),`Lt(y,Mult(2,x))),`Observe(false,Plus(x,Mult(2,y))))),
   `And(`Leq(Mult(2,x),y),`Observe(false,Plus(Mult(2,x),y)))))))

let res1 = qe test1

let _ =
 prerr_endline (pp_prop test1 ^ "\n ===>\n" ^ pp_dnf res1)
