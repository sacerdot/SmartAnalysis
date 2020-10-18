// SPDX-License-Identifier: UNLICENSED

pragma solidity >=0.6.0 <0.8.0;

interface Interf0 {
   function make_a_bet (int a) external;
}

interface Interf1 {
   function bet () external payable;
}

contract Better1 {
   bool _initialized;
   Interf0 better1;
   Interf1 auctioneer;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _better1,address _auctioneer) public {
      if(!_initialized) {
         better1 = Interf0(_better1);
         auctioneer = Interf1(_auctioneer);
         _initialized = true;
      } else {
      }
      return;
   }


   function main (int bet1) public {
      better1.make_a_bet(bet1);
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

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ () public {
      if(!_initialized) {
         _initialized = true;
      } else {
      }
      return;
   }


   function bet () public payable {
      if((int(msg.value) > max)) {
         payable(winner).transfer(uint(max));
         max = int(msg.value);
         winner = msg.sender;
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
