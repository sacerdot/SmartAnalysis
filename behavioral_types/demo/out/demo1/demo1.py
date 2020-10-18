#!/usr/bin/python3
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

if __name__=='__main__':
   w3 = Web3(HTTPProvider('http://localhost:8545'))
   w3.eth.defaultAccount = w3.eth.accounts[0]
   contract_source_path = 'demo1.sol'
   compiled_sol = compile_source_file(contract_source_path)

   Bank_contract_interface = compiled_sol['<stdin>:Bank']
   Bank_address = deploy_contract(w3, Bank_contract_interface, 100).contractAddress
   Bank_contract = (w3.eth.contract(
        address=Bank_address,
        abi=Bank_contract_interface['abi']
    ))
   Thief_contract_interface = compiled_sol['<stdin>:Thief']
   Thief_address = deploy_contract(w3, Thief_contract_interface, 100).contractAddress
   Thief_contract = (w3.eth.contract(
        address=Thief_address,
        abi=Thief_contract_interface['abi']
    ))

   Bank_abi_path = 'Bank_abi.json'
   dump_abi(Bank_abi_path, Bank_contract_interface['abi'])
   Thief_abi_path = 'Thief_abi.json'
   dump_abi(Thief_abi_path, Thief_contract_interface['abi'])

   tx_hash = Bank_contract.functions._init_(Thief_address,Bank_address).transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   tx_hash = Thief_contract.functions._init_().transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)

   print('Bank = ' + Bank_address)
   print('Thief = ' + Thief_address)

   print('Bank abi path = ' + Bank_abi_path)
   print('Thief abi path = ' + Thief_abi_path)

