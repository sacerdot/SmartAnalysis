#!/usr/bin/python3
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
compiled_sol = compile_source_file(contract_source_path)


b_contract_id, b_contract_interface = compiled_sol.popitem()
b_address = deploy_contract(w3, b_contract_interface, 100).contractAddress
b_contract = (w3.eth.contract(
        address=b_address,
        abi=b_contract_interface['abi']
    ))
a_contract_id, a_contract_interface = compiled_sol.popitem()
a_address = deploy_contract(w3, a_contract_interface, 100).contractAddress
a_contract = (w3.eth.contract(
        address=a_address,
        abi=a_contract_interface['abi']
    ))

a_abi_path = 'a_abi.json'
dump_abi(a_abi_path, a_contract_interface['abi'])
b_abi_path = 'b_abi.json'
dump_abi(b_abi_path, b_contract_interface['abi'])

tx_hash = a_contract.functions.init(b_address).transact()
tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
tx_hash = b_contract.functions.init(a_address).transact()
tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)

print('a = ' + a_address)
print('b = ' + b_address)

print('a abi path = ' + a_abi_path)
print('b abi path = ' + b_abi_path)

