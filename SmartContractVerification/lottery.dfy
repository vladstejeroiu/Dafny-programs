include "contract.dfy"

class Lottery extends address {

    var manager: address
    var players: seq<address>
    constructor() 
        ensures manager == this.address

    predicate isManager(caller: address)
        ensures isManager() ==> msg.sender == manager
        {
            manager == msg.sender == manager
        }
    
    method enterPlayerToLottery(player: address) 
        requires player.msg.value > 1
        modifies this
        ensures exists i :: 0 <= i < |players| && players[i] == player
        ensures players == old(players[players:player])
        {
            players := players + [player];
        }

    function random(): int
        ensures 0 <= random() < |players|
    
    method pickWinner()  
        requires |players| > 1
        requires isManager()
        modifies this
        ensures |players| == 0
        ensures this.balance == 0
        {
            var index := random();
            players[index].transfer(this.balance);
        }

    

}