include "contract.dfy"

class Auction extends address {


  var beneficiary: address
  var auctionEnd: nat
  var highestBidder: address?
  var highestBid: nat
  var pendingReturns: map<address, nat>
  var ended: bool


  predicate Valid()
    reads this
  {
      (forall i :: i in pendingReturns ==> this.balance >= pendingReturns[i]) && this.balance >= highestBid
  }

  constructor(biddingTime: nat, seller: address)
    ensures beneficiary == seller && auctionEnd == block.timestamp + biddingTime
    {
      beneficiary := seller;
      msg := new Message();
      block := new Block();
      new;
      auctionEnd := block.timestamp + biddingTime;
      highestBidder := null;
      highestBid := 0;
      ended := false;
      pendingReturns := map[];
    }
  
  method bid(bidder: address)
    requires block.timestamp <= auctionEnd
    requires bidder.msg.value > highestBid
    requires highestBidder != bidder
    requires Valid()
    modifies this
    ensures Valid()
    {
      if highestBidder in pendingReturns{
            pendingReturns := pendingReturns[highestBidder:= (if highestBidder in pendingReturns then pendingReturns[highestBidder] else 0) + highestBid];
      }else {
        pendingReturns := pendingReturns[highestBidder := highestBid];
      }
      assert highestBidder in pendingReturns;
      highestBidder := bidder;
      highestBid := bidder.msg.value;
      this.balance := this.balance + highestBid;
    }

    
    method withdraw(caller: address)
    requires Valid()
    modifies this, caller
    ensures caller in pendingReturns ==> pendingReturns == old(pendingReturns)[caller := 0] 
    ensures Valid() 
      {
        var amount := if caller in pendingReturns then pendingReturns[caller] else 0;
        assert amount <= this.balance;
        pendingReturns := pendingReturns[caller:= 0];
        this.balance := this.balance - amount;
        var sent := caller.send(amount);
      } 


    

  
}