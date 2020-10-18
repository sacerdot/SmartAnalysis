// SPDX-License-Identifier: UNLICENSED

pragma solidity >=0.6.0 <0.8.0;

interface Interf0 {
   function lend (int a) external payable;
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


   function borrow (int n) public {
      Interf0(msg.sender).lend{value: uint(n)}(n);
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


   function lend (int n) public payable {
      payable(msg.sender).transfer(uint((n - 3)));
      return;
   }

   //fallback
   fallback() external payable {
      return;
   }

}
