#! /usr/bin/python3

import json
from web3 import Web3, HTTPProvider

if __name__=='__main__':
   w3 = Web3(HTTPProvider('http://localhost:8545'))
   w3.eth.defaultAccount = w3.eth.accounts[0]

   user1_address = '<WRITE_HERE>'
   user1_abi_path = 'User1_abi.json'
   user2_address = '<WRITE_HERE>'
   user2_abi_path = 'User2_abi.json'
   user3_address = '<WRITE_HERE>'
   user3_abi_path = 'User3_abi.json'
   ponzi_address = '<WRITE_HERE>'
   ponzi_abi_path = 'Ponzi_abi.json'
   bank_address = '<WRITE_HERE>'
   bank_abi_path = 'Bank_abi.json'

   file = open(user1_abi_path,'r')
   user1_abi = json.load(file)
   user1_contract = (w3.eth.contract(address=user1_address, abi=user1_abi))
   file = open(user2_abi_path,'r')
   user2_abi = json.load(file)
   user2_contract = (w3.eth.contract(address=user2_address, abi=user2_abi))
   file = open(user3_abi_path,'r')
   user3_abi = json.load(file)
   user3_contract = (w3.eth.contract(address=user3_address, abi=user3_abi))
   file = open(ponzi_abi_path,'r')
   ponzi_abi = json.load(file)
   ponzi_contract = (w3.eth.contract(address=ponzi_address, abi=ponzi_abi))
   file = open(bank_abi_path,'r')
   bank_abi = json.load(file)
   bank_contract = (w3.eth.contract(address=bank_address, abi=bank_abi))

   print('User1 balance :',str(w3.eth.getBalance(user1_address)))
   print('User2 balance :',str(w3.eth.getBalance(user2_address)))
   print('User3 balance :',str(w3.eth.getBalance(user3_address)))
   print('Ponzi balance :',str(w3.eth.getBalance(ponzi_address)))
   print('Bank balance :',str(w3.eth.getBalance(bank_address)))

   print('wait for transaction...')
   #EXAMPLE OF USE: 'tx_hash = a_contract.functions.main(10).transact()'
   tx_hash = '<WRITE_HERE>'
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   print('User1 balance :',str(w3.eth.getBalance(user1_address)))
   print('User2 balance :',str(w3.eth.getBalance(user2_address)))
   print('User3 balance :',str(w3.eth.getBalance(user3_address)))
   print('Ponzi balance :',str(w3.eth.getBalance(ponzi_address)))
   print('Bank balance :',str(w3.eth.getBalance(bank_address)))

