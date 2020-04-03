contract Bank {

   int x;
   int y;
   bool z;

   (* this is a comment; comments can be nested *)
   function identity(int x) returns (int) {
      int a;
      bool b;
      address c;
      bool y;
      c = msg.sender;
      c = this;
      a = msg.value;
      a = this.balance;
      if (x &lt; 0 == false || false == x &lt; x &amp;&amp; true == (false &amp;&amp; true))
        revert();
      else { return x; }
      b = f();
      y = this.f();
      Thief.f();
      b = Bank.f();
      return -1 * x - 3 * x + x * 4 * -x;
   }

   function test(int x) returns (int) {
      return identity(x);
   }

   function test2() {
     test(3);
     return;
   }

   function test3(int x) returns (int) {
     x = test(3);
     return x;
   }

   function test4(int x, int y) returns (int) {
     x = test(3);
     return y;
   }

   function test5(int x, int y, bool b) returns (int) {
     if(b) { x = test(3); } else { y = test(3); }
     return y;
   }

   function pay(int n) payable {
      if (msg.value &gt;= 1 &amp;&amp; this.balance &gt; n) {
         msg.sender.transfer(n) ;
         msg.sender.ack() ;
      }
   }

   fallback() payable { return; }
}

contract Thief {

   function ack() {
      msg.sender.pay.value(1)(2) ;
   }

   fallback() payable { }
}


(*
Bank bank(100);
Thief thief1(50);
Thief thief2(3);
function main() {
}
*)
