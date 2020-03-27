open Compiler
let python_code =
"#!/usr/bin/python3
import sys
import time
import pprint
import json 

from web3 import Web3, HTTPProvider
from solc import compile_source


def compile_source_file(file_path):
   with open(file_path, 'r') as f:
      source = f.read()

   return compile_source(source)


def deploy_contract(w3, contract_interface, balance):
    contract = w3.eth.contract(
        abi=contract_interface['abi'],
        bytecode=contract_interface['bin'])
    tx_hash = contract.constructor().transact({'value': balance})
    print('waiting for address...')
    address = w3.eth.waitForTransactionReceipt(tx_hash)
    return address

def dump_abi(path, abi):
    with open(path, 'w') as f:
        json.dump(abi, f)

w3 = Web3(HTTPProvider('http://localhost:8545'))
w3.eth.defaultAccount = w3.eth.accounts[0]

contract_source_path = 'out.sol'
compiled_sol = compile_source_file(contract_source_path)\n
"

let address name = name ^ "_address"
let interface name = name ^ "_contract_interface"
let contract name = name ^ "_contract"
let abi_path name = name ^ "_abi_path"

let pp_deploy_contract =
 function 
  | Compiler.Contract (name,_,_,bal) ->
    name ^ "_contract_id, " ^ interface name ^ " = compiled_sol.popitem()\n" ^
    address name ^ " = deploy_contract(w3, " ^ interface name ^ ", " ^
    string_of_int bal ^").contractAddress\n" ^ 
    contract name ^ " = (w3.eth.contract(
        address="^ address name ^",
        abi=" ^ interface name ^ "['abi']
    ))"

let pp_call_init others = 
 function 
  | Contract (name,_,_,_) ->
    "tx_hash = " ^
    contract name ^ ".functions.init(" ^ 
    String.concat "," (List.map (fun (Contract(n,_,_,_)) -> address n) others) ^
    ").transact()\n" ^
    "tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)"

let pp_print_address =
 function 
  | Contract (name,_,_,_) -> 
    "print('" ^ name ^ " = ' + " ^ address name ^ ")"

let pp_save_abi =
 function 
  | Contract (name,_,_,_) -> 
    abi_path name ^ " = '" ^ name ^ "_abi.json'\n" ^
    "dump_abi(" ^ abi_path name ^ ", " ^ interface name ^ "['abi'])"

let pp_print_abi =
 function
  | Contract (name,_,_,_) -> 
    "print('" ^ name ^ " abi path = ' + " ^ abi_path name ^ ")"


let get_python ast =
 let rec aux f1 f2  =
  function
   | [] -> "\n"
   | h :: tl -> f1 h ^ "\n" ^ f2 tl  in
 
 let rec pp_depl_list l = 
  aux pp_deploy_contract pp_depl_list l in
 
 let rec pp_init_list all l =
  aux (fun h -> pp_call_init (List.filter (fun c -> c <> h) all) h )
  (pp_init_list all) l in

 let rec pp_address_list l =
  aux pp_print_address pp_address_list l in

 let rec pp_save_abi_list l =
  aux pp_save_abi pp_save_abi_list l in

 let rec pp_abi_list l =
  aux pp_print_abi pp_abi_list l 

in python_code ^ "\n" ^ pp_depl_list (List.rev ast) ^ pp_save_abi_list ast ^ 
 pp_init_list ast ast ^ pp_address_list ast ^ pp_abi_list ast;;

let outstr =  get_python ((fun (x,_) -> x) Compiler.sol_ast);;
let out_ch = open_out "demo/test.py";;
Printf.fprintf out_ch "%s" outstr;;
