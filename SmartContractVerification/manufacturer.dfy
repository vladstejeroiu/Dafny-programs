include "contract.dfy"

class ProductFactory extends address {

    var deployedProducts: array<address>

    
}


class Manufacturer extends address{    

    var manufacturer: address
    var product: Product
    var retailers: array<Retailer>
    var retailersAddresses: array<address>


    predicate isProducer(msg: Message)
        ensures this.msg.sender == msg.sender == manufacturer

    constructor(name: string, code: string, quantity: nat, price: nat, supplier: address, creator: address)
        ensures manufacturer == creator

    method createNewProduct(name: string, code: string, quantity: nat, price: nat, supplier: address)
        requires name != "" && code != "" && quantity != 0 && price != 0 && supplier != null
        ensures product.productName == name && product.productCode == code && product.minimumQuantity == quantity && product.priceOfOne == price && product.supplierAddress == supplier
        {
            product.productName := name;
            product.productCode := code;
            product.minimumQuantity := quantity;
            product.priceOfOne := price;
            product.supplierAddress := supplier;
            product.created := true;
        }

    
    method orderAProduct(quantity: nat, retailerName: string, caller: address)
        requires product.created
        requires product.minimumQuantity <= quantity
        ensures balance == old(balance) + caller.msg.value
        {
            var retailer  := new Retailer(retailerName, quantity);
            retailers := retailers + [retailer];
        }

        


    
}




class Retailer{
    var retailer: string
    var quantityOrdered: nat

    constructor (r: string, q: nat)
        ensures retailer == r && quantityOrdered == q
}

trait Product{

    var productName: string
    var productCode: string
    var created: bool
    var minimumQuantity: nat
    var priceOfOne: nat
    var supplierAddress: address
    var processed: bool
}