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
   contract_source_path = 'handover_ponzi.sol'
   compiled_sol = compile_source_file(contract_source_path)

   Player_contract_interface = compiled_sol['<stdin>:Player']
   Player_address = deploy_contract(w3, Player_contract_interface, 100).contractAddress
   Player_contract = (w3.eth.contract(
        address=Player_address,
        abi=Player_contract_interface['abi']
    ))
   Player2_contract_interface = compiled_sol['<stdin>:Player2']
   Player2_address = deploy_contract(w3, Player2_contract_interface, 100).contractAddress
   Player2_contract = (w3.eth.contract(
        address=Player2_address,
        abi=Player2_contract_interface['abi']
    ))
   HandoverPonzi_contract_interface = compiled_sol['<stdin>:HandoverPonzi']
   HandoverPonzi_address = deploy_contract(w3, HandoverPonzi_contract_interface, 100).contractAddress
   HandoverPonzi_contract = (w3.eth.contract(
        address=HandoverPonzi_address,
        abi=HandoverPonzi_contract_interface['abi']
    ))

   Player_abi_path = 'Player_abi.json'
   dump_abi(Player_abi_path, Player_contract_interface['abi'])
   Player2_abi_path = 'Player2_abi.json'
   dump_abi(Player2_abi_path, Player2_contract_interface['abi'])
   HandoverPonzi_abi_path = 'HandoverPonzi_abi.json'
   dump_abi(HandoverPonzi_abi_path, HandoverPonzi_contract_interface['abi'])

   tx_hash = Player_contract.functions._init_(HandoverPonzi_address).transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   tx_hash = Player2_contract.functions._init_(HandoverPonzi_address).transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   tx_hash = HandoverPonzi_contract.functions._init_(HandoverPonzi_address,Player_address,Player2_address).transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)

   print('Player = ' + Player_address)
   print('Player2 = ' + Player2_address)
   print('HandoverPonzi = ' + HandoverPonzi_address)

   print('Player abi path = ' + Player_abi_path)
   print('Player2 abi path = ' + Player2_abi_path)
   print('HandoverPonzi abi path = ' + HandoverPonzi_abi_path)

