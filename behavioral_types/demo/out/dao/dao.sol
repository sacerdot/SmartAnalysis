// SPDX-License-Identifier: UNLICENSED

pragma solidity >=0.6.0 <0.8.0;

interface Interf0 {
   function ack () external;
}

interface Interf1 {
   function pay (int a) external payable;
}

contract Bank {
   bool _initialized;

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


   function pay (int n) public payable {
      if(((int(msg.value) >= 1) && (int(address(this).balance) > n))) {
         payable(msg.sender).transfer(uint(n));
         Interf0(msg.sender).ack();
      } else {
      }
      return;
   }

   //fallback
   fallback() external payable {
      return;
   }

}

contract Thief {
   bool _initialized;

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


   function ack () public {
      Interf1(msg.sender).pay{value: uint(1)}(2);
      return;
   }

   //fallback
   fallback() external payable {
      return;
   }

}
