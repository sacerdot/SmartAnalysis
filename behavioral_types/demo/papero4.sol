(* max gain: 0
   max loss: max([nat(Punta1),nat(-Bank_max+Punta1)]) 
*)

contract Participant1 {

   function main(int punta1) {
       Participant1.punta(punta1);
   }

   function punta(int n) {
      Bank.puntata.value(n)();
   }
   
   fallback() payable { }

}

contract Bank {

   int max;
   address winner;

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
