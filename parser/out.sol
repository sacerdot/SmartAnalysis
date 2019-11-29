pragma solidity 0.4.25;
interface Interf0{

}
interface Interf1{

}
interface Interf2{
function foo(string calldata , address ) payable external returns (int );
}
interface Interf3{

}
contract c {
mapping (string => int) symbol;
Interf1 p;
int weight = 2;
Interf0 d;
bool initialize = false;
constructor() payable public {

}
function init(address _d) public {
if (!initialize){
d = Interf0(_d);
initialize = true;
}
}
function foo(int r, bool b) payable public returns (int ){
weight = 2;
weight = 3;
return weight;
}
function fie() payable public returns (string memory ){

return 'Catched!';
}
}
contract d {
mapping (string => int) symbol;
Interf2 c;
int r = 0;
bool initialize = false;
constructor() payable public {
symbol['a'] = 0;

}
function init(address _c) public {
if (!initialize){
c = Interf2(_c);
initialize = true;
}
}
function loop() payable public returns (int ){

return 5;
}
function foo(string memory s, address con) payable public returns (int ){
r = 0;
r = ((8 > 9) ? 8 : 9);
r = symbol['a'];
r = this.loop();
r = c.foo(s, address(this));
return r;
}
}