# Demo

## Geth

### Installazione Geth

Per installare geth è prima necessario installare Go dal [sito](https://golang.org/dl/), dopodiché:

```
git clone https://github.com/ethereum/go-ethereum.git
cd go-ethereum
make geth
```

### Creazione di un nuovo account nella rete

Bisogna prima creare la cartella dei dati di Ethereum

```
mkdir gethDataDir
geth account new --datadir gethDataDir
```

### Creazione del genesis block

Il genesis block è il primo blocco nella blockchain, per crearlo è necessario innanzitutto creare il file json `genesis.block` all'interno di `gethDataDir`:
```
{
    "config": {
        "chainId": 17,
        "eip150Block": 0,
        "eip155Block": 0,
        "eip158Block": 0,
        "homesteadBlock": 0,
        "byzantiumBlock": 0,
        "constantinopleBlock": 0,
        "petersburgBlock": 0
    },
    "difficulty": "1",
    "gasLimit": "2100000",
    "alloc":{
        "yourNewlyCreatedAccountAddressMustGoHere": {
            "balance": "40000"
        }
    },
}
```
+ **config:** configurazione per settare le variabili relative a Ethereum. 
    + **chainid:** identificativo relativo al nodo della rete: se settato a 1 si avrà un nodo della rete globale, altrimenti un nodo della rete locale. 
    + **homesteadBlock, byzantiumBlock,...:** quando settati a 0 indicano che si usa quella release di Ethereum
    + **eip150Block, ...** Ethereum Improvement Proposal, standard che aggiungono e migliorano la piattaforma Ethereum
+ **difficulty:** gas massimo per ogni blocco
+ **gasLimit:** difficoltà di mining
+ **alloc:** Per ogni account permette di specificare il balance iniziale

Dopo aver creato il json è necessario inizializzare la blockchain:
```
cd gethDataDir
geth --datadir gethDataDir/ init genesis.json
```

### Far partire Ethereum

```
geth --mine --minerthreads=1 --datadir gethDataDir --rpc --rpcport 8545 --networkid 17 --allow-insecure-unlock
```

+ **--mine --minerthreads=1:** permette di fare il mining sulla rete privata
+ **--datadir:** specifica la cartella dei dati di Ethereum
+ **--rpc --rpcport 8545:** abilita il server HTTP nell'indirizzo di localhost e in ascolto sulla porta 8545
+ **--networkid 17:** specifica l'id del nodo, che deve essere uguale al `chainId` specificato nel `genesis.json`
+ **--allow-insecure-unlock:** permette di sbloccare gli account

### Console JavaScript

È possibile interagire con il server tramite una console JavaScript:
```
geth attach ipc:gethDataDir/geth.ipc
```

All'interno della quale è necessario sbloccare l'account:
```
personal.unlockAccount(eth.accounts[0], password, 0)
```

## Dipendenze Python

Per poter eseguire il codice Python è necessario installare la libreria per compilare in Solidity, e la libreria per interagire con Ethereum:
```
pip install py-solc
pip install web3
```
