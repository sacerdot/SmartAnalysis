import json
from web3 import Web3, HTTPProvider
from test import c_address, c_abi_path
w3 = Web3(HTTPProvider('http://localhost:8545'))

w3.eth.defaultAccount = w3.eth.accounts[0]

file = open(c_abi_path, 'r')
c_abi = json.load(file)

c_contract = (w3.eth.contract(
    address=c_address,
    abi=c_abi
    ))
print(c_contract.functions.fie().call())
