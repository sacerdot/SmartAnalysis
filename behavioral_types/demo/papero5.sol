(* Scenario 1:
     Player participates to the following Ponzi scheme,
     immediately followed by Player2.
     max loss: 0
     max gain: 7/20 N

   Scenario 2 (comment out line 52):
     max loss: N
     max gain: 0
*)

contract Player {
    int amount;
    
    function main(int n) {
        amount = n;
        HandoverPonzi.init(n);
    }
    
    function cont() {
        HandoverPonzi.join.value(amount)();
    }

    fallback() payable { }
}

contract Player2 {
    function cont(int n) {
        HandoverPonzi.join.value(n)();
    }

    fallback() payable { }
}

contract HandoverPonzi {
  address owner ;
  address user ;
  int price ;

  function init(int n) {
    owner = HandoverPonzi ;
    user = HandoverPonzi ;
    price = n ;
    Player.cont();
  }

  function sweepCommission (int amount) {
    if (msg.sender == owner) owner.send(amount) ;
  }
  
  function join() payable {
    if (msg.value < price) revert() ;
    user.transfer(9 * msg.value / 10) ;
    user = msg.sender ;
    price = 3 * price / 2;
    (* comment next line for scenario 2 *)
    if (msg.sender == Player) Player2.cont(price);
  }
}
