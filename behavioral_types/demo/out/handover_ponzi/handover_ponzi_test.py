#! /usr/bin/python3

import json
from web3 import Web3, HTTPProvider

if __name__=='__main__':
   w3 = Web3(HTTPProvider('http://localhost:8545'))
   w3.eth.defaultAccount = w3.eth.accounts[0]

   player_address = '<WRITE_HERE>'
   player_abi_path = 'Player_abi.json'
   player2_address = '<WRITE_HERE>'
   player2_abi_path = 'Player2_abi.json'
   handoverPonzi_address = '<WRITE_HERE>'
   handoverPonzi_abi_path = 'HandoverPonzi_abi.json'

   file = open(player_abi_path,'r')
   player_abi = json.load(file)
   player_contract = (w3.eth.contract(address=player_address, abi=player_abi))
   file = open(player2_abi_path,'r')
   player2_abi = json.load(file)
   player2_contract = (w3.eth.contract(address=player2_address, abi=player2_abi))
   file = open(handoverPonzi_abi_path,'r')
   handoverPonzi_abi = json.load(file)
   handoverPonzi_contract = (w3.eth.contract(address=handoverPonzi_address, abi=handoverPonzi_abi))

   print('Player balance :',str(w3.eth.getBalance(player_address)))
   print('Player2 balance :',str(w3.eth.getBalance(player2_address)))
   print('HandoverPonzi balance :',str(w3.eth.getBalance(handoverPonzi_address)))

   print('wait for transaction...')
   #EXAMPLE OF USE: 'tx_hash = a_contract.functions.main(10).transact()'
   tx_hash = '<WRITE_HERE>'
   tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
   print('Player balance :',str(w3.eth.getBalance(player_address)))
   print('Player2 balance :',str(w3.eth.getBalance(player2_address)))
   print('HandoverPonzi balance :',str(w3.eth.getBalance(handoverPonzi_address)))

