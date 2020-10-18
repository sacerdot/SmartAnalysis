#! /usr/bin/python3

import json
from web3 import Web3, HTTPProvider

if __name__=='__main__':
   w3 = Web3(HTTPProvider('http://localhost:8545'))
   w3.eth.defaultAccount = w3.eth.accounts[0]

   bank_address = '<WRITE_HERE>'
   bank_abi_path = 'Bank_abi.json'
   thief_address = '<WRITE_HERE>'
   thief_abi_path = 'Thief_abi.json'

   file = open(bank_abi_path,'r')
   bank_abi = json.load(file)
   bank_contract = (w3.eth.contract(address=bank_address, abi=bank_abi))
   file = open(thief_abi_path,'r')
   thief_abi = json.load(file)
   thief_contract = (w3.eth.contract(address=thief_address, abi=thief_abi))

   print('Bank balance :',str(w3.eth.getBalance(bank_address)))
   print('Thief balance :',str(w3.eth.getBalance(thief_address)))

   print('wait for transaction...')
   #EXAMPLE OF USE: 'tx_hash = a_contract.functions.main(10).transact()'
   tx_hash = '<WRITE_HERE>'
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   print('Bank balance :',str(w3.eth.getBalance(bank_address)))
   print('Thief balance :',str(w3.eth.getBalance(thief_address)))

