// SPDX-License-Identifier: UNLICENSED

pragma solidity >=0.6.0 <0.8.0;

interface Interf0 {
   function join () external payable;
   function init () external;
}

interface Interf1 {
   function go () external;
}

interface Interf2 {

}

contract User1 {
   bool _initialized;
   Interf0 ponzi;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _ponzi) public {
      if(!_initialized) {
         ponzi = Interf0(_ponzi);
         _initialized = true;
      } else {
      }
      return;
   }


   function main () public {
      ponzi.init();
      return;
   }


   function go () public {
      ponzi.join{value: uint(110)}();
      return;
   }

}

contract User2 {
   bool _initialized;
   Interf0 ponzi;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _ponzi) public {
      if(!_initialized) {
         ponzi = Interf0(_ponzi);
         _initialized = true;
      } else {
      }
      return;
   }


   function go () public {
      ponzi.join{value: uint(110)}();
      return;
   }

}

contract User3 {
   bool _initialized;
   Interf0 ponzi;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _ponzi) public {
      if(!_initialized) {
         ponzi = Interf0(_ponzi);
         _initialized = true;
      } else {
      }
      return;
   }


   function go () public {
      ponzi.join{value: uint(110)}();
      return;
   }

}

contract Ponzi {
   bool _initialized;
   address owner1;
   address owner2;
   address owner3;
   int first;
   int last;
   Interf0 ponzi;
   Interf1 user1;
   Interf2 bank;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _ponzi,address _user1,address _bank) public {
      if(!_initialized) {
         ponzi = Interf0(_ponzi);
         user1 = Interf1(_user1);
         bank = Interf2(_bank);
         _initialized = true;
      } else {
      }
      return;
   }


   function init () public {
      owner1 = address(ponzi);
      owner2 = address(ponzi);
      owner3 = address(ponzi);
      first = 1;
      last = 1;
      user1.go();
      return;
   }


   function push (address addr) public {
      if((last == 1)) {
         owner1 = addr;
      } else {
         if((last == 2)) {
            owner2 = addr;
         } else {
            if((last == 3)) {
               owner3 = addr;
            } else {
               revert();
            }

         }

      }
      last = (last + 1);
      if((int(address(this).balance) >= 150)) {
         this.pop();
      } else {
      }
      return;
   }


   function pop () public {
      address res;
      if((first >= last)) {
         return;
      } else {
      }
      if((first == 1)) {
         res = owner1;
      } else {
         if((first == 2)) {
            res = owner2;
         } else {
            if((first == 3)) {
               res = owner3;
            } else {
               revert();
            }

         }

      }
      first = (first + 1);
      payable(res).transfer(uint(150));
      return;
   }


   function join () public payable {
      if(!(int(msg.value) == 110)) {
         revert();
      } else {
      }
      payable(address(bank)).transfer(uint(10));
      this.push(msg.sender);
      return;
   }

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

}
