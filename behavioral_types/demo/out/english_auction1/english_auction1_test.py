#! /usr/bin/python3

import json
from web3 import Web3, HTTPProvider

if __name__=='__main__':
   w3 = Web3(HTTPProvider('http://localhost:8545'))
   w3.eth.defaultAccount = w3.eth.accounts[0]

   better1_address = '<WRITE_HERE>'
   better1_abi_path = 'Better1_abi.json'
   auctioneer_address = '<WRITE_HERE>'
   auctioneer_abi_path = 'Auctioneer_abi.json'

   file = open(better1_abi_path,'r')
   better1_abi = json.load(file)
   better1_contract = (w3.eth.contract(address=better1_address, abi=better1_abi))
   file = open(auctioneer_abi_path,'r')
   auctioneer_abi = json.load(file)
   auctioneer_contract = (w3.eth.contract(address=auctioneer_address, abi=auctioneer_abi))

   print('Better1 balance :',str(w3.eth.getBalance(better1_address)))
   print('Auctioneer balance :',str(w3.eth.getBalance(auctioneer_address)))

   print('wait for transaction...')
   #EXAMPLE OF USE: 'tx_hash = a_contract.functions.main(10).transact()'
   tx_hash = '<WRITE_HERE>'
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   print('Better1 balance :',str(w3.eth.getBalance(better1_address)))
   print('Auctioneer balance :',str(w3.eth.getBalance(auctioneer_address)))

