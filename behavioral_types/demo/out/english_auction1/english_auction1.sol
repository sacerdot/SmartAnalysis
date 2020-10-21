// SPDX-License-Identifier: UNLICENSED

pragma solidity >=0.6.0 <0.8.0;

interface Interf0 {
   function bet () external payable;
   function init (int a) external;
}

interface Interf1 {
   function make_a_bet (int a) external;
}

contract Better1 {
   bool _initialized;
   Interf0 auctioneer;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _auctioneer) public {
      if(!_initialized) {
         auctioneer = Interf0(_auctioneer);
         _initialized = true;
      } else {
      }
      return;
   }


   function main (int bet1) public {
      auctioneer.init(bet1);
      return;
   }


   function make_a_bet (int n) public {
      auctioneer.bet{value: uint(n)}();
      return;
   }

   //fallback
   fallback() external payable {
      return;
   }

}

contract Auctioneer {
   bool _initialized;
   int max;
   address winner;
   Interf0 auctioneer;
   Interf1 better1;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _auctioneer,address _better1) public {
      if(!_initialized) {
         auctioneer = Interf0(_auctioneer);
         better1 = Interf1(_better1);
         _initialized = true;
      } else {
      }
      return;
   }


   function init (int bet1) public {
      max = 0;
      winner = address(auctioneer);
      better1.make_a_bet(bet1);
      return;
   }


   function bet () public payable {
      if((int(msg.value) > max)) {
         payable(winner).transfer(uint(max));
      } else {
         payable(msg.sender).transfer(msg.value);
      }
      return;
   }

   //fallback
   fallback() external payable {
      return;
   }

}
