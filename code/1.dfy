
method Main() {
    print Lsd(10,10,10), "\n";
    assert pence(Lsd(10,10,10)) == 2 * pence(Lsd(5,5,5));

    var total := add(Lsd(0,2,6),Lsd(0,2,6));
    assert total == Lsd(0,5,0);
    var tot := add(Lsd(0,10,6),Lsd(0,10,6));
    assert tot == Lsd(1,1,0);
}
//Given the following datatype for https://en.wikipedia.org/wiki/£sd 
datatype Lsd = Lsd(pounds : nat, shillings : nat, pence : nat)

//write this predicate that ensures the datatype represents a valid amount of Lsd
predicate ValidLsd( amount : Lsd )
  requires 0 <= amount.pounds
  requires 0 <= amount.shillings < 20
  requires 0 <= amount.pence < 12
{

  1 == 1;

}

//covnert an Lsd to an equivalent amount of just pence
function method pence( amount : Lsd ) : nat 
  requires ValidLsd(amount)
{
  
  amount.pounds*240+amount.shillings*12+amount.pence;

}

//convert some pence back to an equivalent Lsd
function method lsd( pence : nat ) : (sum : Lsd) 
  requires 0 <= pence
  ensures ValidLsd(sum)  
{

  var pounds:nat, shillings:nat, pence:nat;
  pounds := pence / 240;
  shillings := pence % 240 / 12;
  pence := pence - sum.shillings;
  sum := Lsd(pounds, shillings, pence);

}

//add two amounts of Lsd returning a valid Lsd
method add( a1 : Lsd, a2 : Lsd) returns ( sum : Lsd ) 
  requires ValidLsd(a1)
  requires ValidLsd(a2)
  ensures ValidLsd(sum)
{

  var pounds:nat, shillings:nat, pence:nat;
  pounds := a1.pounds + a2.pounds;
  shillings := a1.shillings + a2.shillings;
  pence := a1.pence + a2.pence;
  sum := Lsd(pounds, shillings, pence);

}

//subtract a2 from a1 returninga valid Lsd
method sub( a1 : Lsd, a2 : Lsd) returns ( sub : Lsd ) 
  requires ValidLsd(a1)
  requires ValidLsd(a2)
  ensures ValidLsd(sum)
{

  var pounds:nat, shillings:nat, pence:nat;
  pounds := a1.pounds - a2.pounds;
  shillings := a1.shillings - a2.shillings;
  pence := a1.pence - a2.pence;
  sum := Lsd(pounds, shillings, pence);
  
}

//https://en.wikipedia.org/wiki/Guinea_(coin)
//Lawyers bills and gambling debts are traditionally paid in guineas.
//Convert an amount of Lsd in to some number of guineas and the balance in mundane Lsd.
method guineas(a : Lsd ) returns ( guineas:  nat, mundane : Lsd ) 
{
  
}

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

//your definition should be able to verify the following methods

method addPreservesValue(a1 : Lsd, a2: Lsd) returns (a3 : Lsd)
  requires ValidLsd(a1)
  requires ValidLsd(a2)
  ensures  ValidLsd(a3)
  ensures  pence(a1) + pence(a2) == pence(a3)
{
    a3 := add(a1,a2);
}

method SubPreservesValue(a1 : Lsd, a2: Lsd) returns (a3 : Lsd)
  requires ValidLsd(a1)
  requires ValidLsd(a2)
  requires pence(a1) > pence(a2)
  ensures  ValidLsd(a3)
  ensures  pence(a1) - pence(a2) == pence(a3)
{
    a3 := sub(a1,a2);
} 

method guineasPreservesValue(a1 : Lsd) returns (g : int, a2 : Lsd)
 requires ValidLsd(a1)
  ensures ValidLsd(a2)
  ensures pence(a1) == pence(a2) + (g * 21 * 12)
{
    g, a2 := guineas(a1);

}
