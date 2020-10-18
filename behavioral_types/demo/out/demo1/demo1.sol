// SPDX-License-Identifier: UNLICENSED

pragma solidity >=0.6.0 <0.8.0;

interface Interf0 {
   function f () external;
}

interface Interf1 {
   function f () external returns (bool);
}

interface Interf2 {
   function ack () external;
}

interface Interf3 {
   function pay (int a) external payable;
}

contract Bank {
   bool _initialized;
   int x;
   int y;
   bool z;
   Interf0 thief;
   Interf1 bank;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _thief,address _bank) public {
      if(!_initialized) {
         thief = Interf0(_thief);
         bank = Interf1(_bank);
         _initialized = true;
      } else {
      }
      return;
   }


   function identity (int x) public returns (int) {
      int a;
      bool b;
      address c;
      bool y;
      c = msg.sender;
      c = address(this);
      a = int(msg.value);
      a = int(address(this).balance);
      if((((0 > x) == false) || ((false == (x > x)) && (true == (false && true))))) {
         revert();
      } else {
         return x;
      }
      b = this.f();
      y = this.f();
      thief.f();
      b = bank.f();
      return (((-1 * x) - (3 * x)) + ((x * 4) * -x));
   }


   function foo (int x) public returns (int) {
      return this.foo(x);
   }


   function foo1 (int x) public returns (int) {
      return this.foo2(x);
   }


   function foo2 (int x) public returns (int) {
      return this.foo1(x);
   }


   function test (int x) public returns (int) {
      return this.identity(x);
   }


   function test2 () public {
      this.test(3);
      return;
   }


   function test3 (int x) public returns (int) {
      x = this.test(3);
      return x;
   }


   function test4 (int x,int y) public returns (int) {
      x = this.test(3);
      return y;
   }


   function test5 (int x,int y,bool b) public returns (int) {
      if(b) {
         x = this.test(3);
      } else {
         y = this.test(3);
      }
      return y;
   }


   function test6 () public returns (int) {
      this.test5(0,0,true);
      return 2;
   }


   function pay (int n) public payable {
      if(((int(msg.value) >= 1) && (int(address(this).balance) > n))) {
         payable(msg.sender).transfer(uint(n));
         Interf2(msg.sender).ack();
      } else {
      }
      return;
   }

   //fallback
   fallback() external payable {
      this.foo(3);
      this.foo1(3);
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
      Interf3(msg.sender).pay{value: uint(1)}(2);
      return;
   }

   //fallback
   fallback() external payable {
      return;
   }

}
