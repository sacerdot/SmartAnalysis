open Unsigned
open Utils

type interface = IID     of string
type address   = ADDR_of of interface
type uint      = Unsigned.UInt32.t
type byte      = Unsigned.UInt8.t
type 'a array  = 'a list
type bytes     = byte array

(* Note on arrays (from solidity docs):
   [..]an array of 5 dynamic arrays of uint is written as uint[][5]. 
   The notation is reversed compared to some other languages. 
   In Solidity, X[3] is always an array containing three elements 
   of type X, even if X is itself an array. 
   This is not the case in other languages such as C.
   [..]Indices are zero-based, and access is in the opposite 
   direction of the declaration.
   
  [EXAMPLE OF USE - ARRAY] an array of 5 dynamic arrays of uint is written as uint[][5].
  So,write it: Array(Array(UInt,None),Some 5)
*)
type _ tag =
 | Unit : unit tag
 | Int  : int tag
 | UInt : uint tag
 | Byte : byte tag
 | Bool : bool tag
 | Address   : address tag
 | Interface : interface tag
 | String : string tag (*string is equal to bytes but does not allow length or index access.*)
 | Bytes  : bytes tag (*bytes is similar to byte[], but it is packed tightly in calldata and memory.*)
 | Array  : 'a tag * int option -> 'a array tag
 | Mapping : 'a tag * 'b tag -> ('a*'b) tag (*'a tag,'b tag must be Int,UInt,Byte,Bool,Address,String,Bytes,Array. Mapping or Unit tag are not allowed.*)
type _ tag_list =
 | TNil  : unit tag_list
 | TCons : 'a tag * 'b tag_list -> ('a * 'b) tag_list

type storage    = Storage   | Memory  | Calldata | NoStorage (*data location*)
type view       = View      | Pure    | Payable | NoView
type visibility = External  | Public  | Internal  | Private | NoVisibility

type ('a,'b) meth = 'a tag * 'b tag_list * string

type 'a ident = 'a tag * string
type 'a field = 'a ident
type 'a var   = 'a ident

type any_field =
 | AnyField : _ field * interface option -> any_field
type fields = any_field list
type _ expr =
 | Var   : 'a var -> 'a expr 
 | This  : interface expr
 | Field : 'a field -> 'a expr
(* [NOTE ON ARRAY] : Indices are zero-based, and access is in the opposite direction of the declaration. 
 So, write GetValueArray(GetValueArray(Var((Array(Array(UInt,Some 3),Some 5)),"tmp"),4),2) 
 to access last element of matrix tmp. *)
 | GetValueArray : 'a array expr * int -> 'a expr
 | GetValueMapping : ('a*'b) expr * 'a expr -> 'b expr
 | New : 'a array tag * int -> 'a array expr
 | Plus   : int expr * int expr -> int expr
 | Minus  : int expr * int expr -> int expr
 | Mult   : int expr * int expr -> int expr
 | Div    : int expr * int expr -> int expr
 | UMinus : int expr -> int expr
 | Geq : int expr * int expr -> bool expr
 | Gt  : int expr * int expr -> bool expr
 | Eq  : 'a tag * 'a expr * 'a expr -> bool expr
 | And : bool expr * bool expr -> bool expr
 | Or  : bool expr * bool expr -> bool expr
 | Not : bool expr -> bool expr
 | Value : 'a -> 'a expr
 | MsgSender : address expr
 | MsgValue  : uint expr
 | Balance   : address expr -> uint expr
 | IntToUInt : int expr -> uint expr
 | UIntToInt : uint expr -> int expr
 | InterfaceToAddress : interface expr -> address expr
 | AddressToInterface : interface * address expr -> interface expr
 | OnAddressCall : address expr -> interface expr
type 'a tagged_expr = 'a tag * 'a expr

type _ var_list =
 | VNil  : unit var_list
 | VCons : 'a var * 'b var_list -> ('a * 'b) var_list
type _ expr_list =
 | ENil  : unit expr_list
 | ECons : 'a expr * 'b expr_list -> ('a * 'b) expr_list
type _ lhs =
 | LField : 'a field -> 'a lhs
 | LVar   : 'a var -> 'a lhs
 | LSetArray   : 'a array lhs * int -> 'a lhs
 | LSetMapping : ('a*'b) lhs * 'a expr -> 'b lhs
 | LDiscard : unit lhs
type _ rhs =
 | Expr : 'a expr -> 'a rhs
 | Call : interface expr * ('a,'b) meth * uint expr option * 'b expr_list -> 'a rhs
type (_,_) stm =
 | Epsilon   : (_,[`Epsilon]) stm
 | ReturnRhs : 'a rhs -> ('a,_) stm
 | Return : (unit,_) stm
 | Assign : 'a lhs * 'a rhs * ('b,'c) stm -> ('b,'c) stm
 | IfThenElse : bool expr * ('b,[`Epsilon]) stm * ('b,[`Epsilon]) stm * ('b,'c) stm -> ('b,'c) stm
 | Revert : _ stm

type ('a,'b) block =
 Block : 'b var_list * visibility * view * _ var_list * ('a,[`Return]) stm -> ('a,'b) block

type any_method_decl =
 | AnyMethDecl : ('a,'b) meth * ('a,'b) block -> any_method_decl
type methods   = any_method_decl list
type any_funct = 
 | AnyFunct : ('a,'b) meth * 'b var_list * visibility * view -> any_funct
type functions = any_funct list

type an_interface =
 AInterface : interface * functions -> an_interface
(*address * optional constructor * methods * optional fallback * fields *)
type a_contract =
 AContract : string * (unit,unit) block option * methods * (unit,unit) block option * fields -> a_contract
type configuration = an_interface list * a_contract list

type (_,_) eq = Refl : ('a,'a) eq
let rec eq_tag : type a b. a tag -> b tag -> (a,b) eq option = fun t1 t2 ->
 match t1,t2 with
 | Unit, Unit -> Some Refl
 | Int, Int -> Some Refl
 | Bool, Bool -> Some Refl
 | UInt, UInt -> Some Refl
 | Byte, Byte -> Some Refl
 | Address, Address -> Some Refl
 | Interface, Interface -> Some Refl
 | String, String -> Some Refl
 | Bytes, Bytes -> Some Refl
 | Array(t1,d1), Array(t2,d2) -> (match eq_tag t1 t2 with | Some Refl -> if d1=d2 then Some Refl else None | None -> None)
 | Mapping(a1,b1), Mapping(a2,b2) ->
    let res1 = eq_tag a1 a2 in
    let res2 = eq_tag b1 b2 in
    (match res1,res2 with | (Some Refl),(Some Refl) -> Some Refl | _,_ -> None)
 | _,_ -> None

let rec eq_tag_list : type a b. a tag_list -> b tag_list -> (a,b) eq option =
 fun tl1 tl2 ->
 match tl1,tl2 with
  | TNil,TNil -> Some Refl
  | TCons(t1,tl1),TCons(t2,tl2) ->
     (match eq_tag t1 t2 with
         None -> None
       | Some Refl ->
          match eq_tag_list tl1 tl2 with
             None -> None
           | Some Refl -> Some Refl)
  | _,_ -> None

let rec tag_of_lhs : type a. a lhs -> a tag =
 function
  | LField f -> Utils.fst2 f 
  | LVar v -> Utils.fst2 v
  | LSetArray (set,_) ->
     (match tag_of_lhs set with
     | Array(ty,dim) -> ty
     | Bytes -> Byte
     | _ -> assert false)
  | LSetMapping (set,_) -> 
     (match tag_of_lhs set with
     | Mapping(a,b) -> b
     | _ -> assert false)
  | LDiscard -> Unit

let tag_of_meth : type a. (a,'b) meth -> a tag =
 function
 | UInt,_,_ -> UInt
 | Byte,_,_ -> Byte
 | Unit,_,_ -> Unit
 | Int,_,_ -> Int
 | Bool,_,_ -> Bool
 | Address,_,_ -> Address
 | Bytes,_,_ -> Bytes
 | String,_,_ -> String
 | Array(t,s),_,_ -> Array(t,s) 
 | _ -> assert false

let rec tag_of_expr_array : type a. a expr -> a tag =
 function
 | Var(t,n) | Field(t,n) -> t 
 | New(t,s) -> t
 | GetValueArray(set,s) -> 
   (match tag_of_expr_array set with
   | Array(ty,dim) -> ty
   | Bytes -> Byte
   | _ -> assert false)
 | _ -> assert false

let rec tag_of_key_mapping : type a b. (a * b) expr -> a tag =
 function
 | Var(Mapping(k,v),n) -> k
 | Field(Mapping(k,v),n) -> k
 | GetValueArray(set,_) as x -> 
   (match tag_of_expr_array x with
   | Mapping(k,v) -> k
   | _ -> assert false)
 | _ -> assert false

let rec tag_of_key_mapping_lhs : type a b. (a * b) lhs -> a tag =
 function
 | LVar(Mapping(k,_),_) -> k
 | LField(Mapping(k,_),_) -> k
 | LSetArray(set,_) as x -> 
   (match tag_of_lhs x with
   | Mapping(k,_) -> k
   | _ -> assert false)
 | LSetMapping(set,_) as x ->
   (match tag_of_lhs x with
   | Mapping(k,_) -> k
   | _ -> assert false)
 | _ -> assert false

let rec tag_list_length : type a. a tag_list -> int =
 function
    TNil -> 0
  | TCons(_,tl) -> 1 + tag_list_length tl

let rec var_list_length : type a. a var_list -> int =
 function
    VNil -> 0
  | VCons(_,tl) -> 1 + var_list_length tl

let rec expr_list_map :
 type c. < f: 'a. 'a tag -> 'a expr -> 'b > -> c tag_list -> c expr_list-> 'b list
= fun o tl el ->
 match tl,el with
    TNil,ENil -> []
  | TCons(t,tl),ECons(e,el) -> o#f t e :: expr_list_map o tl el

(*** Serialization ***)
let mk_indent indent = String.make (3 * indent) ' '

let pp_storage : storage -> string =
 function
  Storage -> "storage"
  | Memory -> "memory"
  | Calldata -> "calldata"
  | NoStorage -> ""

let rec pp_tag : type a. a tag -> string =
 function
  | Unit -> assert false
  | Int -> "int"
  | Bool -> "bool"
  | UInt -> "uint"
  | Byte -> "byte"
  | Address -> "address"
  | Interface -> "interface"
  | String -> "string"
  | Bytes -> "bytes"
  | Array(t,s) -> pp_tag t ^"["^(match s with Some x -> string_of_int x | None -> "")^"]"
  | Mapping(t1,t2) -> "mapping("^pp_tag t1^" => "^pp_tag t2^")"

let pp_view : view -> string =
 function
 | View -> "view"
 | Pure -> "pure"
 | Payable -> "payable"
 | NoView -> ""

let pp_visibility : visibility -> string =
 function
 | External -> "external"
 | Public -> "public"
 | Internal -> "internal"
 | Private -> "private"
 | NoVisibility -> ""

let rec pp_tag_list : type a. a tag_list -> string list =
 function
  | TNil -> []
  | TCons(x,tl) -> pp_tag x :: pp_tag_list tl
let pp_decl (t,s) = pp_tag t ^ " " ^ s
let pp_ident (_t,s) = (*pp_tag t ^ " " ^*) s
let pp_var (i,n) = pp_ident (i,n)
let rec pp_var_list : type a. a var_list -> string list =
 function
  | VNil -> []
  | VCons(v,tl) -> pp_decl v :: pp_var_list tl

let pp_interface : interface -> string = 
 function IID(x) -> x

let pp_address : address -> string = 
 function ADDR_of(x) -> pp_interface x

let rec pp_value (type a) (tag : a tag) (v : a) =
 match tag with
  | Unit -> assert false (* it should not happen *)
  | Mapping(t1,t2) -> assert false (* it should not happen *)
  | Int -> string_of_int v
  | UInt -> string_of_int (Unsigned.UInt32.to_int v)
  | Byte -> string_of_int (Unsigned.UInt8.to_int v)
  | Bool -> string_of_bool v
  | Address -> pp_address v
  | Interface -> pp_interface v
  | String -> v
  | Bytes -> pp_value_array tag v
  | Array(t,s) -> pp_value_array tag v
and pp_value_array: type a. a tag -> a -> string =
 fun t v -> match t with
 | Array(Int,s) -> "["^(String.concat "," (List.map string_of_int v))^"]"
 | Array(UInt,s) -> pp_value_array (Array(Int,s)) ((List.map Unsigned.UInt32.to_int) v)
 | Bytes -> pp_value_array (Array(Int,None)) ((List.map Unsigned.UInt8.to_int) v)
 | Array(Byte,s) -> pp_value_array (Array(Int,s)) ((List.map Unsigned.UInt8.to_int) v)
 | Array(Bool,s) -> "["^(String.concat "," (List.map string_of_bool v))^"]"
 | Array(Address,s) -> "["^(String.concat "," (List.map pp_address v))^"]"
 | Array(Interface,s) -> assert false
 | Array(x,s) -> "["^(String.concat "," (List.map (pp_value_array x) v))^"]"
 | _ -> assert false

let pp_field = pp_ident
let pp_any_field (AnyField((t,n) as f,opt)) = (match opt with Some IID(x) -> x^" "^n | None -> pp_decl f)
let pp_fields ~indent l =
 String.concat "" (List.map (fun f -> mk_indent indent ^ pp_any_field f ^ ";\n") l)

let rec pp_expr : type a. a tag -> a expr -> string =
 fun tag ->
 function
  | Var (v) -> pp_var v
  | This -> "this"
  | Field f -> pp_field f
  | GetValueArray (e,i) -> pp_expr (tag_of_expr_array e) e ^ "["^string_of_int i^"]"
  | GetValueMapping (mapping,key) -> 
      let key_tag = tag_of_key_mapping mapping in
      (pp_expr (Mapping(key_tag,tag)) mapping)^"["^(pp_expr (tag_of_key_mapping mapping) key)^"]"
  | New (t,i) -> "new "^pp_tag t^"("^string_of_int i^")"
  | Plus (e1,e2) -> "(" ^ pp_expr tag e1 ^ " + " ^ pp_expr tag e2 ^ ")"
  | Minus (e1,e2) -> "(" ^ pp_expr tag e1 ^ " - " ^ pp_expr tag e2 ^ ")"
  | Mult (c,e) -> "(" ^ pp_expr tag c ^ " * " ^ pp_expr tag e ^ ")"
  | Div (c,e) -> "(" ^ pp_expr tag c ^ " / " ^ pp_expr tag e ^ ")"
  | UMinus e -> "-" ^ pp_expr tag e
  | Geq (e1,e2) -> "(" ^ pp_expr Int e1 ^ " >= " ^ pp_expr Int e2 ^ ")"
  | Gt (e1,e2) -> "(" ^ pp_expr Int e1 ^ " > " ^ pp_expr Int e2 ^ ")"
  | Eq (tag,e1,e2) -> "(" ^ pp_expr tag e1 ^ " == " ^ pp_expr tag e2 ^ ")"
  | And (g1,g2) -> "(" ^ pp_expr tag g1 ^ " && " ^ pp_expr tag g2 ^ ")"
  | Or (g1,g2) -> "(" ^ pp_expr tag g1 ^ " || " ^ pp_expr tag g2 ^ ")"
  | Not g -> "!" ^ pp_expr tag g
  | Value v -> pp_value tag v
  | IntToUInt x -> "uint("^pp_expr Int x^")"
  | UIntToInt x -> "int("^pp_expr UInt x^")"
  | MsgSender -> "msg.sender"
  | MsgValue -> "msg.value"
  | Balance e -> pp_expr Address e ^".balance"
  | AddressToInterface(i,e) -> pp_interface i ^ "("^pp_expr Address e ^")"
  | InterfaceToAddress(e) -> "address("^pp_expr Interface e^")" 
  | OnAddressCall addr -> "payable("^pp_expr Address addr^")"

let pp_tagged_expr e = pp_expr (fst e) (snd e)

let rec pp_expr_list : type a. a tag_list -> a expr_list -> string list = fun tg el ->
 match tg,el with
    TNil,ENil -> []
   | TCons(tag,tagl),ECons(v,tl) -> pp_expr tag v :: pp_expr_list tagl tl

let pp_meth ?(verbose=false) (rtag,tags,id) =
 if verbose then
  id ^ ":(" ^ String.concat "*" (pp_tag_list tags) ^ " -> " ^ pp_tag rtag ^ ")"
 else
  id

let rec pp_lhs : type a. a lhs -> string =
 function
  | LField f -> pp_field f ^ " = "
  | LVar v -> pp_var v ^ " = "
  | LSetArray (set,i) as x -> (pp_lhs_array_ident x)^(pp_lhs_array_index x)^" = "
  | LSetMapping(set,key) -> (pp_lhs_mapping set)^"["^(pp_expr (tag_of_key_mapping_lhs set) key)^"] = "
  | LDiscard -> ""
and pp_lhs_mapping : type a b. (a*b) lhs -> string =
 function
 | LField f -> pp_field f
 | LVar v -> pp_var v
 | LSetArray(set,i) as x -> (pp_lhs_array_ident x)^(pp_lhs_array_index x)
 | LSetMapping(set,key) -> (pp_lhs_mapping set)^"["^(pp_expr (tag_of_key_mapping_lhs set) key)^"]"
and pp_lhs_array_index : type a. a lhs -> string =
 function
 | LSetArray(s,i) -> (pp_lhs_array_index s)^"[" ^string_of_int i ^ "]"
 | _ -> ""
and pp_lhs_array_ident : type a. a lhs -> string =
 function
 | LSetArray((LField f),_) -> pp_field f
 | LSetArray((LVar v),_) -> pp_var v
 | LSetArray(s,_) -> pp_lhs_array_ident s
 | _ -> assert false

let pp_rhs tag =
 function
  | Expr e -> pp_expr tag e
  | Call(addr,((_,_,name) as meth),value,exprl) ->
     pp_expr Interface addr ^
     "." ^pp_meth meth^
     (match value with 
        None -> "" 
      | Some v -> "{value: "^(pp_expr UInt v)^ "}") ^
     "(" ^
      String.concat "," (pp_expr_list (Utils.snd3 meth) exprl) ^")"

let rec pp_stm : type a b. indent:int -> ?breakline:bool -> a tag -> (a,b) stm -> string = fun ~indent ?(breakline=true) tag stm ->
 (match stm with Epsilon -> "" | _ -> mk_indent indent) ^
 (match stm with
  | Epsilon -> ""
  | ReturnRhs e -> "return " ^ pp_rhs tag e ^ ";"
  | Return -> "return;"
  | Assign(lhs,rhs,stm) ->
     pp_lhs lhs ^
     pp_rhs (tag_of_lhs lhs) rhs ^ ";" ^
     (match stm with Epsilon -> "" | _ -> "\n") ^
     pp_stm ~indent ~breakline:false tag stm
  | IfThenElse(c,stm1,stm2,stm3) ->
     "if(" ^ pp_expr Bool c ^") {\n" ^
     pp_stm ~indent:(indent+1) tag stm1 ^
     mk_indent indent ^ "} else {\n" ^
     pp_stm ~indent:(indent+1) tag stm2 ^
     mk_indent indent ^ "}\n" ^
     pp_stm ~indent ~breakline:false tag stm3
  | Revert -> "revert();") ^
 (match stm with Epsilon -> "" | _ when breakline -> "\n" | _ -> "")

let pp_block : type a. indent:int -> a tag -> (a, 'b) block -> string =
fun ~indent tag (Block (vl,vis,view,lvl,stm)) ->
 strip("(" ^ String.concat "," (pp_var_list vl) ^ ") " ^
 pp_visibility vis ^ " " ^ pp_view view ^ " " ^
 (match tag with Unit -> "" | _ -> "returns (" ^ pp_tag tag ^ ")"))^
 " {\n" ^
 String.concat "" (List.map (fun s -> mk_indent (indent+1) ^ s ^ ";\n") (pp_var_list lvl)) ^
 pp_stm ~indent:(indent+1) tag stm ^
 mk_indent indent ^ "}\n\n"

let pp_any_method_decl ~indent (AnyMethDecl(m,b)) =
 mk_indent indent ^
 "function " ^ pp_meth m ^ " " ^ pp_block ~indent (Utils.fst3 m) b

let pp_methods ~indent l =
 String.concat "\n" (List.map (pp_any_method_decl ~indent) l)

let pp_any_funct ~indent (AnyFunct(m,vl,vis,view)) =
 let tag = Utils.fst3 m in
 mk_indent indent ^
 Utils.strip("function " ^ pp_meth m ^ " " ^
 "(" ^ String.concat "," (pp_var_list vl) ^ ") " ^
 pp_visibility vis ^ " " ^ pp_view view ^ " " ^
 (match tag with Unit -> "" | _ -> "returns (" ^ pp_tag tag ^ ")"))^ ";"

let pp_functions ~indent l =
 String.concat "\n" (List.map (pp_any_funct ~indent) l)

let pp_constructor ~indent =
 function
    None -> ""
  | Some b -> mk_indent indent ^ "constructor" ^ pp_block ~indent Unit b

let pp_fallback ~indent =
 function
    None -> ""
  | Some b -> mk_indent indent^"//fallback\n"^
    mk_indent indent ^ "fallback" ^ pp_block ~indent Unit b

let pp_an_interface (AInterface (interf,functs)) =
 "interface " ^ pp_interface interf ^ " {\n" ^
 pp_functions ~indent:1 functs ^
 "\n}\n"

let pp_a_contract (AContract (addr,constructor,methods,fallback,fields)) =
 "contract " ^ addr ^ " {\n" ^
 pp_fields ~indent:1 fields ^ "\n" ^
 pp_constructor ~indent:1 constructor ^ "\n" ^
 pp_methods ~indent:1 methods ^
 pp_fallback ~indent:1 fallback ^
 "}\n"

let pp_configuration x y (i,c) =
 "// SPDX-License-Identifier: UNLICENSED\n\n"^
 "pragma solidity >="^x^" <"^y^";\n\n"^
 String.concat "\n"
  (List.map pp_an_interface i)
 ^"\n"^
 String.concat "\n"
  (List.map pp_a_contract c)