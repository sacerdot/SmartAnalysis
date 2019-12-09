pragma solidity 0.4.25;
interface Interf0{
function addbalance() payable external returns (int );
}
interface Interf1{
function addbalance() payable external returns (int );
}
contract a {
mapping (string => int) symbol;
int x = 0;
Interf0 b;
bool initialize = false;
constructor() payable public {

}
function init(address _b) public {
if (!initialize){
b = Interf0(_b);
initialize = true;
}
}
function addbalance() payable public returns (int ){

return int(msg.value);
}
function getbalance() payable public returns (int ){

return int(this.balance);
}
function transf_tob(int v) payable public returns (int ){
x = 0;
if (int(this.balance) >= v){
x = b.addbalance.value(uint(v))();
}
else {
x = 0;
}
return x;
}
}
contract b {
mapping (string => int) symbol;
int x = 0;
Interf1 a;
bool initialize = false;
constructor() payable public {

}
function init(address _a) public {
if (!initialize){
a = Interf1(_a);
initialize = true;
}
}
function addbalance() payable public returns (int ){

return int(msg.value);
}
function getbalance() payable public returns (int ){

return int(this.balance);
}
function transf_toa(int v) payable public returns (int ){
x = 0;
if (int(this.balance) >= v){
x = a.addbalance.value(uint(v))();
}
else {
x = 0;
}
return x;
}
}