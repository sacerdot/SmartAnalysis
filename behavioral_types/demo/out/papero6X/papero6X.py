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
   contract_source_path = 'papero6X.sol'
   compiled_sol = compile_source_file(contract_source_path)

   User1_contract_interface = compiled_sol['<stdin>:User1']
   User1_address = deploy_contract(w3, User1_contract_interface, 100).contractAddress
   User1_contract = (w3.eth.contract(
        address=User1_address,
        abi=User1_contract_interface['abi']
    ))
   User2_contract_interface = compiled_sol['<stdin>:User2']
   User2_address = deploy_contract(w3, User2_contract_interface, 100).contractAddress
   User2_contract = (w3.eth.contract(
        address=User2_address,
        abi=User2_contract_interface['abi']
    ))
   Ponzi_contract_interface = compiled_sol['<stdin>:Ponzi']
   Ponzi_address = deploy_contract(w3, Ponzi_contract_interface, 100).contractAddress
   Ponzi_contract = (w3.eth.contract(
        address=Ponzi_address,
        abi=Ponzi_contract_interface['abi']
    ))
   Bank_contract_interface = compiled_sol['<stdin>:Bank']
   Bank_address = deploy_contract(w3, Bank_contract_interface, 100).contractAddress
   Bank_contract = (w3.eth.contract(
        address=Bank_address,
        abi=Bank_contract_interface['abi']
    ))

   User1_abi_path = 'User1_abi.json'
   dump_abi(User1_abi_path, User1_contract_interface['abi'])
   User2_abi_path = 'User2_abi.json'
   dump_abi(User2_abi_path, User2_contract_interface['abi'])
   Ponzi_abi_path = 'Ponzi_abi.json'
   dump_abi(Ponzi_abi_path, Ponzi_contract_interface['abi'])
   Bank_abi_path = 'Bank_abi.json'
   dump_abi(Bank_abi_path, Bank_contract_interface['abi'])

   tx_hash = User1_contract.functions._init_(Ponzi_address).transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   tx_hash = User2_contract.functions._init_(Ponzi_address).transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   tx_hash = Ponzi_contract.functions._init_(Ponzi_address,User1_address,Bank_address).transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   tx_hash = Bank_contract.functions._init_().transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)

   print('User1 = ' + User1_address)
   print('User2 = ' + User2_address)
   print('Ponzi = ' + Ponzi_address)
   print('Bank = ' + Bank_address)

   print('User1 abi path = ' + User1_abi_path)
   print('User2 abi path = ' + User2_abi_path)
   print('Ponzi abi path = ' + Ponzi_abi_path)
   print('Bank abi path = ' + Bank_abi_path)

