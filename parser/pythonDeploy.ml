open Compiler
let python_code =
"#!/usr/bin/python3
import sys
import time
import pprint

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

w3 = Web3(HTTPProvider('http://localhost:8545'))
w3.eth.defaultAccount = w3.eth.accounts[0]

contract_source_path = '" ^ Compiler.sol_filename ^ "'
compiled_sol = compile_source_file(contract_source_path)\n
"

let address name = name ^ "_address"
let interface name = name ^ "_contract_interface"
let contract name = name ^ "_contract"

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
    contract name ^ ".functions.init(" ^ 
    String.concat "," (List.map (fun (Contract(n,_,_,_)) -> address n) others) ^
    ").call()"

let pp_print_address =
 function 
  | Contract (name,_,_,_) -> 
    "print('" ^ name ^ " = ' + " ^ address name ^ ")"

let get_python ast =
 let rec pp_depl_list = 
  function
   | [] -> "\n"
   | h :: tl -> pp_deploy_contract h ^ "\n" ^ pp_depl_list tl in
 let rec pp_init_list all =
  function 
   | [] -> "\n"
   | h :: tl -> pp_call_init (List.filter (fun c -> c <> h) all) h ^ "\n" ^
   pp_init_list all tl in
 let rec pp_address_list =
  function 
   | [] -> "\n"
   | h :: tl -> pp_print_address h ^ "\n" ^ pp_address_list tl 
in python_code ^ "\n" ^ pp_depl_list (List.rev ast) ^ pp_init_list ast ast ^ pp_address_list ast;;

let outstr =  get_python ((fun (x,_) -> x) Compiler.sol_ast);;
let out_ch = open_out "test.py";;
Printf.fprintf out_ch "%s" outstr;;
