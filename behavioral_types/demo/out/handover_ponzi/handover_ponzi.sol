// SPDX-License-Identifier: UNLICENSED

pragma solidity >=0.6.0 <0.8.0;

interface Interf0 {
   function join () external payable;
   function init (int a) external;
}

interface Interf1 {
   function cont () external;
}

interface Interf2 {
   function cont (int a) external;
}

contract Player {
   bool _initialized;
   int amount;
   Interf0 handoverPonzi;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _handoverPonzi) public {
      if(!_initialized) {
         handoverPonzi = Interf0(_handoverPonzi);
         _initialized = true;
      } else {
      }
      return;
   }


   function main (int n) public {
      amount = n;
      handoverPonzi.init(n);
      return;
   }


   function cont () public {
      handoverPonzi.join{value: uint(amount)}();
      return;
   }

   //fallback
   fallback() external payable {
      return;
   }

}

contract Player2 {
   bool _initialized;
   Interf0 handoverPonzi;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _handoverPonzi) public {
      if(!_initialized) {
         handoverPonzi = Interf0(_handoverPonzi);
         _initialized = true;
      } else {
      }
      return;
   }


   function cont (int n) public {
      handoverPonzi.join{value: uint(n)}();
      return;
   }

   //fallback
   fallback() external payable {
      return;
   }

}

contract HandoverPonzi {
   bool _initialized;
   address owner;
   address user;
   int price;
   Interf0 handoverPonzi;
   Interf1 player;
   Interf2 player2;

   constructor() public payable {
      _initialized = false;
      return;
   }


   function _init_ (address _handoverPonzi,address _player,address _player2) public {
      if(!_initialized) {
         handoverPonzi = Interf0(_handoverPonzi);
         player = Interf1(_player);
         player2 = Interf2(_player2);
         _initialized = true;
      } else {
      }
      return;
   }


   function init (int n) public {
      owner = address(handoverPonzi);
      user = address(handoverPonzi);
      price = n;
      player.cont();
      return;
   }


   function sweepCommission (int amount) public {
      if((msg.sender == owner)) {
         payable(owner).send(uint(amount));
      } else {
      }
      return;
   }


   function join () public payable {
      if((price > int(msg.value))) {
         revert();
      } else {
      }
      payable(user).transfer(uint(((9 * int(msg.value)) / 10)));
      user = msg.sender;
      price = ((3 * price) / 2);
      if((msg.sender == address(player))) {
         player2.cont(price);
      } else {
      }
      return;
   }

   //fallback
   fallback() external payable {
      return;
   }

}
