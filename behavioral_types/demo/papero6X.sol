contract User1 {
    function main() {
        Ponzi.init();
    }
    
    function go() {
        Ponzi.join.value(110)();
    }
}

contract User2 {

    function go() {
        Ponzi.join.value(110)();
    }
    
}

(*contract User3 {

    function go() {
        Ponzi.join.value(110)();
    }
    
}*)

(*contract User4 {

    function go() {
        Ponzi.join.value(110)();
    }
    
}*)

contract Ponzi {
    address owner1;
    address owner2;
    (*address owner3;*)
    (*address owner4;*)
    (*address owner5;*)
    int first;
    int last;
    
    function init() {
        owner1 = Ponzi;
        owner2 = Ponzi;
        (*owner3 = Ponzi;*)
        (*owner4 = Ponzi;*)
        (*owner5 = Ponzi;*)
        first = 1;
        last = 1;
        
        User1.go();
    }
    
    function push(address addr) {
        if(last == 1){
            owner1 = addr;
        }else{
            if(last == 2){
               owner2 = addr;
            }(*else{
              if (last == 3){
                owner3 = addr;
              }*)
        (*else if (last == 4) owner4 = addr;*)
        (*else if (last == 5) owner5 = addr;*)
              else{
                revert();
              }
            (*}*)
        }

        last = last + 1;
        if (this.balance >= 150) pop();
    }
    
    function pop() {
        address res;
        if (first >= last){ return;}
        
        if (first == 1){ 
            res = owner1;
        }else{
            if (first == 2){
                res = owner2;
            }(*else{
                if (first == 3){ 
                   res = owner3;
                }*)
        (*else if (first == 4) res = owner4;*)
        (*else if (first == 5) res = owner5;*)
                else{ 
                   revert(); 
                }
            (*}*)
        }
        first = first + 1;
        
        res.transfer(150);
    }
    
    function join() payable {
        if (msg.value != 110) revert() ;
        Bank.transfer(10);
        push(msg.sender);
    }
}

contract Bank {
    
}
