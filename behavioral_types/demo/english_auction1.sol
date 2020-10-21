(* max gain: 0
   max loss: Bet1
*)

contract Better1 {

   function main(int bet1) {
       Auctioneer.init(bet1);
   }

   function make_a_bet(int n) {
      Auctioneer.bet.value(n)();
   }
   
   fallback() payable { }
}

contract Auctioneer {

   int max;
   address winner;

   function init(int bet1) {
       max = 0;
       winner = Auctioneer;
       Better1.make_a_bet(bet1);
   }


   function bet() payable {
       if(max < msg.value) {
           winner.transfer(max);
       (*    max = msg.value;
           winner = msg.sender; *)
       } else {
           msg.sender.transfer(msg.value);
       }
   }

   fallback() payable { }
}
