pragma solidity 0.4.25;
interface Interf0{

}
interface Interf1{

}
interface Interf2{

}
interface Interf3{
function dep(int , bool , address , address ) payable external returns (int );
}
interface Interf4{
function foo(string calldata , address ) payable external returns (int );
}
interface Interf5{

}
contract c {
mapping (string => int) symbol;
Interf2 q;
Interf1 p;
int weight = 2;
Interf0 d;
int retval = 0;
bool initialize = false;
constructor() payable public {

}
function init(address _d) public {
if (!initialize){
d = Interf0(_d);
}
}
function foo(string memory s, address k) payable public returns (int ){
retval = 0;
q = Interf2(address(d));
retval = (Interf3(k)).dep.value((uint)(4))(4, true, address(p), address(q));
retval = (this).foo('ciao', k);
return retval;
}
}
contract d {
mapping (string => int) symbol;
Interf4 c;
int r = 0;
bool initialize = false;
constructor() payable public {

}
function init(address _c) public {
if (!initialize){
c = Interf4(_c);
}
}
function foo(string memory s, address con) payable public returns (int ){
r = 0;
r = (c).foo(s, address(this));
return r;
}
}