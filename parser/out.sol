pragma solidity 0.5.11;
interface banca{
function dep(int , bool ) payable public returns (int );
function foo(string memory , address ) payable public returns (int )
}


interface branca{

}
interface cianca{

}
contract c {
mapping (string => int) symbol;
int weight = 2;
int retval = 0;
bool cond = true;
address p ;
address r ;
address w ;
constructor() public{
symbol[a] = 0;
}
function dep(int x, bool b) payable public returns (int ){
retval = ((((5 * weight) > 4) ? (5 * weight) : 4) + (int)(address(this).balance));
weight = symbol['a'];

if ((x == 0)){
weight = (weight - 1);
}
else {
weight = ((int)(msg.value) + (int)(address(this).balance));
}
return 1;
}
function foo(string memory s, address k) payable public returns (int ){

s = 'ciao';
cond = (retval == 9);
retval = ((banca)k).dep.value((uint)(4))(4, true);
return retval;
}
}
contract d {
int w = 2;
int r = 0;
address f ;
address e ;

function dep(int x, bool b) payable public returns (int ){
if (true){
w = (w - 1);
}
else {
w = (1 + (int)(address(this).balance));
}
return 1;
}
function foo(string memory s, address c) payable public returns (int ){

s = 'ciao';
r = ((banca)c).foo(s, f);
return r;
}
}