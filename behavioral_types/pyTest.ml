open Solidity

let indent = "   "
let py_fst = 
"#! /usr/bin/python3

import json
from web3 import Web3, HTTPProvider

if __name__=='__main__':\n"
^indent^"w3 = Web3(HTTPProvider('http://localhost:8545'))\n"
^indent^"w3.eth.defaultAccount = w3.eth.accounts[0]\n\n"

let address = "_address"
let abi_path = "_abi_path"
let abi_js = "_abi.json"
let abi = "_abi"
let contract = "_contract"

let pp_addr_abi =
 function
  | Solidity.AContract (name,_,_,_,_) ->
    let lower = String.uncapitalize_ascii name in 
    indent^lower^address^" = '<WRITE_HERE>'\n"^
    indent^lower^abi_path^" = '"^name^abi_js^"'"

let pp_load_file =
 function
 | Solidity.AContract (name,_,_,_,_) ->
    let lower = String.uncapitalize_ascii name in 
    indent^"file = open("^lower^abi_path^",'r')\n"
    ^indent^lower^abi^" = json.load(file)\n"
    ^indent^lower^contract^" = (w3.eth.contract(address="^lower^address^
    ", abi="^lower^abi^"))"

let pp_balance =
 function
 | Solidity.AContract (name,_,_,_,_) ->
     let lower = String.uncapitalize_ascii name in 
     indent^"print('"^name^" balance :',str(w3.eth.getBalance("^lower^address^")))"

let pp_transaction =
 indent^"print('wait for transaction...')\n"^
 indent^"#EXAMPLE OF USE: 'tx_hash = a_contract.functions.main(10).transact()'\n"^
 indent^"tx_hash = '<WRITE_HERE>'\n"^
 indent^"tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)\n"

let get_python ast =
 let rec aux f1 f2  =
  function
   | [] -> "\n"
   | h :: tl -> f1 h ^ "\n" ^ f2 tl  in
 
 let rec pp_addr_abi_list l =
  aux pp_addr_abi pp_addr_abi_list l in 

 let rec pp_balance_list l =
  aux pp_balance pp_balance_list l in 
  
 let rec pp_load_file_list l =
  aux pp_load_file pp_load_file_list l in

  py_fst^pp_addr_abi_list ast^pp_load_file_list ast^
  pp_balance_list ast^pp_transaction^pp_balance_list ast^""