(* max gain: 0
   max loss: Punta1
*)

contract Participant1 {

   function main(int punta1) {
       Bank.init(punta1);
   }

   function punta(int n) {
      Bank.puntata.value(n)();
   }
   
   fallback() payable { }

}

contract Bank {

   int max;
   address winner;

   function init(int punta1) {
       max = 0;
       winner = Bank;
       Participant1.punta(punta1);
   }


   function puntata() payable {
       if(max < msg.value) {
           winner.transfer(max);
           max = msg.value;
           winner = msg.sender;
       } else {
           msg.sender.transfer(msg.value);
       }
   }

   fallback() payable { }


}
