pragma solidity 0.5.11;
contract c {
    int balance = 0;
    int weight = 2;
    int retval = 0;
    function dep(bool b, int x) public returns (int){
        retval = ((4 > 3) ? 4 : 3);
        if (((0 > x) && b)){
            weight = (1 + (-weight));
        }
        else {
            balance = 1;
        }
        return 1;
    }
    function foo(string memory s) public returns (int){
        s = 'ciao';
        retval = dep(true, 4);
        return retval;
    }
}
