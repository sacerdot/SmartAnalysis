#!/usr/bin/python3
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

contract_source_path = 'out.sol'
compiled_sol = compile_source_file(contract_source_path)


d_contract_id, d_contract_interface = compiled_sol.popitem()
d_address = deploy_contract(w3, d_contract_interface, 3).contractAddress
d_contract = (w3.eth.contract(
        address=d_address,
        abi=d_contract_interface['abi']
    ))
c_contract_id, c_contract_interface = compiled_sol.popitem()
c_address = deploy_contract(w3, c_contract_interface, 10).contractAddress
c_contract = (w3.eth.contract(
        address=c_address,
        abi=c_contract_interface['abi']
    ))

c_contract.functions.init(d_address).call()
d_contract.functions.init(c_address).call()

print('c = ' + c_address)
print('d = ' + d_address)

