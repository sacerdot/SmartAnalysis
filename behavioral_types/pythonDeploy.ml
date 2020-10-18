open Solidity

let indent = "   "

let python_code = fun name ->
"#!/usr/bin/python3
import sys
import time
import pprint
import json 

from web3 import Web3, HTTPProvider
from solcx import compile_source


def compile_source_file(file_path):
   with open(file_path, 'r') as f:
      source = f.read()

   return compile_source(source, evm_version='petersburg')


def deploy_contract(w3, contract_interface, balance):
    contract = w3.eth.contract(
        abi=contract_interface['abi'],
        bytecode=contract_interface['bin'])
    print('Deploy contract with balance',balance)
    tx_hash = contract.constructor().transact({'value': balance})
    print('waiting for address...')
    address = w3.eth.waitForTransactionReceipt(tx_hash)
    return address

def dump_abi(path, abi):
    with open(path, 'w') as f:
        json.dump(abi, f)

if __name__=='__main__':\n"
^indent^
"w3 = Web3(HTTPProvider('http://localhost:8545'))\n"
^indent^
"w3.eth.defaultAccount = w3.eth.accounts[0]\n"
^indent^
"contract_source_path = '"^name^"'\n"
^indent^
"compiled_sol = compile_source_file(contract_source_path)\n"

let address name = name ^ "_address"
let interface name = name ^ "_contract_interface"
let contract name = name ^ "_contract"
let abi_path name = name ^ "_abi_path"

let pp_deploy_contract =
 function 
  | Solidity.AContract (name,_,_,_,_) ->
    indent^interface name^" = compiled_sol['<stdin>:"^name^"']\n" ^
    indent^address name ^ " = deploy_contract(w3, " ^ interface name ^ ", " ^
    "100" ^").contractAddress\n" ^ indent^
    contract name ^ " = (w3.eth.contract(
        address="^ address name ^",
        abi=" ^ interface name ^ "['abi']
    ))"

let rec get_interf_fields: Solidity.fields -> string list = 
 function
 | Solidity.AnyField((_,name),Some _)::t -> 
    [String.capitalize_ascii(name)]@(get_interf_fields t)
 | h::t -> get_interf_fields t
 | [] -> []

let pp_call_init others = 
 function 
 | Solidity.AContract (name,_,_,_,_fields) ->
    let names = get_interf_fields _fields in
    indent^"tx_hash = " ^
    contract name ^ ".functions._init_(" ^ 
    String.concat "," (List.map (fun n -> address n) names) ^
    ").transact()\n" ^
    indent^"tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)"

let pp_print_address =
 function 
 | Solidity.AContract (name,_,_,_,_) -> 
    indent^"print('" ^ name ^ " = ' + " ^ address name ^ ")"

let pp_save_abi =
 function 
 | Solidity.AContract (name,_,_,_,_) -> 
    indent^abi_path name ^ " = '" ^ name ^ "_abi.json'\n" ^
    indent^"dump_abi(" ^ abi_path name ^ ", " ^ interface name ^ "['abi'])"

let pp_print_abi =
 function
 | Solidity.AContract (name,_,_,_,_) -> 
    indent^"print('" ^ name ^ " abi path = ' + " ^ abi_path name ^ ")"


let get_python ast name =
 let rec aux f1 f2  =
  function
   | [] -> "\n"
   | h :: tl -> f1 h ^ "\n" ^ f2 tl  in
 
 let rec pp_depl_list l = 
  aux pp_deploy_contract pp_depl_list l in
 
 let rec pp_init_list all l =
  aux (fun h -> pp_call_init all h )
  (pp_init_list all) l in

 let rec pp_address_list l =
  aux pp_print_address pp_address_list l in

 let rec pp_save_abi_list l =
  aux pp_save_abi pp_save_abi_list l in

 let rec pp_abi_list l =
  aux pp_print_abi pp_abi_list l in 

 (python_code name)^ "\n" ^ pp_depl_list (ast)^pp_save_abi_list ast ^ 
 pp_init_list ast ast ^ pp_address_list ast ^ pp_abi_list ast;;