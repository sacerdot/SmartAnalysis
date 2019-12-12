import json
from web3 import Web3, HTTPProvider
w3 = Web3(HTTPProvider('http://localhost:8545'))

w3.eth.defaultAccount = w3.eth.accounts[0]

a_address = "0xc878011D952ccd7D85e52F3912A6f37Ad66E6c4b"
a_abi_path = "a_abi.json"


b_address = "0x4c6D601c00B11deE40E76D6ce6B917d7FaBF5768"
b_abi_path = "b_abi.json"

file = open(a_abi_path, 'r')
a_abi = json.load(file)

a_contract = (w3.eth.contract(
    address=a_address,
    abi=a_abi
    ))

file = open(b_abi_path, 'r')
b_abi = json.load(file)

b_contract = (w3.eth.contract(
    address=b_address,
    abi=b_abi
    ))

tx_hash = a_contract.functions.transf_tob(10).transact()
tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)

print(str(w3.eth.getBalance(a_address)))
print(str(w3.eth.getBalance(b_address)))
