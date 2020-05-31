contract Bank {

   function borrow(int n) {
      msg.sender.lend.value(n)(n);
   }

   fallback() payable { }
}

contract Thief {

   function lend(int n) payable {
      msg.sender.transfer(n-3) ;
   }

   fallback() payable { }
}
