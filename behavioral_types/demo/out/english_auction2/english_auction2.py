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
   contract_source_path = 'english_auction2.sol'
   compiled_sol = compile_source_file(contract_source_path)

   Better1_contract_interface = compiled_sol['<stdin>:Better1']
   Better1_address = deploy_contract(w3, Better1_contract_interface, 100).contractAddress
   Better1_contract = (w3.eth.contract(
        address=Better1_address,
        abi=Better1_contract_interface['abi']
    ))
   Auctioneer_contract_interface = compiled_sol['<stdin>:Auctioneer']
   Auctioneer_address = deploy_contract(w3, Auctioneer_contract_interface, 100).contractAddress
   Auctioneer_contract = (w3.eth.contract(
        address=Auctioneer_address,
        abi=Auctioneer_contract_interface['abi']
    ))

   Better1_abi_path = 'Better1_abi.json'
   dump_abi(Better1_abi_path, Better1_contract_interface['abi'])
   Auctioneer_abi_path = 'Auctioneer_abi.json'
   dump_abi(Auctioneer_abi_path, Auctioneer_contract_interface['abi'])

   tx_hash = Better1_contract.functions._init_(Better1_address,Auctioneer_address).transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   tx_hash = Auctioneer_contract.functions._init_().transact()
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)

   print('Better1 = ' + Better1_address)
   print('Auctioneer = ' + Auctioneer_address)

   print('Better1 abi path = ' + Better1_abi_path)
   print('Auctioneer abi path = ' + Auctioneer_abi_path)

