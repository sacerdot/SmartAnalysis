contract Bank {

   function pay(int n) payable {
      if (msg.value >= 1 && this.balance > n) {
         msg.sender.transfer(n) ;
         msg.sender.ack() ;
      }
   }

   fallback() payable { }
}

contract Thief {

   function ack() {
      msg.sender.pay.value(1)(2) ;
   }
}
