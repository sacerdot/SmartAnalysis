pragma solidity 0.5.11;

interface pInt {

}

interface qInt {

}

interface dInt {

}

interface kInt {
        function dep(int, bool, address, address) payable external returns(int);
}

contract c {
    dInt d ;  /* gli altri */

    int weight = 2;
    pInt p ;
    qInt q ;
    bool initialized = false ;

    constructor() public{
    }

    function init(address d) {
        if initialized then fine del mondo
            else {
                initialized = true ;
                this.d = (dInt) d ;
            }
    }

    function foo(string memory s, address k) payable public returns (int ){
        this.q = (qInt) d  /* attenzione: assegnamento deve dare al lhs anche i metodi del rhs
                              oppure fare ereditare il lhs dal rhs
                              oppure ottieni l'address e poi lo ricasti :-)
                           */
        retval = ((kInt) k).dep.value(4)(4, true, p, q);
        return retval;
    }
}

/* Piu' codice bash/python/* che faccia

pcontract = deploy_contract(c,10)
dcontract = deploy_contract(d,3)
pcontract.init(dcontract);
dcontract.init(pcontract);
print("p=" pcontract)
print("d=" dcontract)

*/
