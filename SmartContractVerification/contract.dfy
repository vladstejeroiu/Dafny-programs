//Formal Verification of Smart Contracts Using Dafny

trait address{

    var balance: nat
    var msg: Message
    var block: Block

    
    method transfer(payer: address) returns (r: bool)
        requires this != payer
        modifies this, payer
        ensures balance == old(balance) + old(payer.balance) 
        ensures fallback(payer)
        {
            balance := balance + payer.balance;
            payer.balance := 0;
            r := fallback(payer);
        }

    function method fallback(payer:address): bool
        reads this, payer
        {
            if payer.balance == 0 then true else false
        }

    method send(amount: nat) returns (r: bool)
        modifies this
        ensures this.balance > amount ==> balance == old(balance) + old(amount)
        ensures !(this.balance > amount) ==> !r
        {
            if (this.balance > amount){
                balance := balance + amount;
                var amount := 0;
                r := true;
            } else {
                r := false;
            }
        }

}


class Message {

    var sender: seq<char>
    var value: nat
    var data: nat

    constructor()
        ensures sender in test.listofAddresses()
        ensures value == 100
        
}

class Block{

    var timestamp: nat
    var coinbase: address
    var difficulty: nat
    var gaslimit: nat
    var number: nat

    constructor()
        ensures timestamp == 1592537964
}

module test{

    function listofAddresses() :seq<seq<char>>
    {        
        [
        "0x0EfD2fEC66633f663F05e952dC21FdF1EBc9BB67",
        "0xcb24700E70C5EcadbBA188363DB49D7d48BFE14d",
        "0xB651923e174Ff80b22Eb2202E146b026752002B1",
        "0xBf5a0508e458747c1207db30706113CEE03f1f48",
        "0xD7F92FbCAd676EAC52ca4D65467877D5bdcC88BB",
        "0xCf5cfd7f3d59a3ac90691734c10459fFB48A1d14",
        "0xC66EA0BFa181c8649AB845eB4211329Ff064587F",
        "0x5b7189Ed2A62737aadB25e7f04654f12f9392d00",
        "0x957bed47125B0311b31447aBa58554214A287246",
        "0x583031D1113aD414F02576BD6afaBfb302140225",
        "0xdD870fA1b7C4700F2BD7f44238821C26f7392148"
        ]
    }
}