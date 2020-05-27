contract Bank {

   function borrow(int n) {
      msg.sender.lend.value(n)(n);
   }

}

contract Thief {

   function lend(int n) payable {
      msg.sender.transfer(n-3) ;
   }

}
