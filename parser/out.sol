pragma solidity 0.5.11;

interface banca{
function fie(int , bool ) payable external returns (int );
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
symbol['a'] = 0;
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
retval = (banca(k)).fie.value((uint)(4))(4, true);
return retval;
}
}
contract d {
int w = 2;
int r = 0;
address f ;
address e ;

function dep2(int x, bool b) payable public returns (int ){
if (true){
w = (w - 1);
}
else {
w = (1 + (int)(address(this).balance));
}
return 1;
}
function foo(string memory s, address con) payable public returns (int ){

s = 'ciao';
r = (c(con)).foo(s, f);
return r;
}
}