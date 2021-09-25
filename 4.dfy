datatype Option<T> = None | Some(e:T)
datatype Cash<K(==), V(==)> =
    Empty|
    Bucket(key:K, history:seq<V>, rest:Cash<K,V>)
/* Hint dafny is not likely to know if the history is empty or not. */

function method size<K,V>(csh:Cash<K,V>):nat decreases csh {
  match csh
    case Empty => 0
    case Bucket(_,_,rest) => 1+ size(rest)
}

// add an entry, consisting of the key k and value a single element 
// sequence [v], to the cash c. Return the new cash////
function method Add<K(==),V(==)> ( kin:K, vin:V, c: Cash<K,V>) :Cash<K,V> 
 decreases c
{
    match c
    case Empty => Cash(kin, vin, Empty)
    case Bucket(key , history , rest) => Cash(key, history+[k], c)
}

// return the last element added to the the cash for key
function method Lookup<K(==),V(==)>(csh:Cash<K,V>, key:K) :Option<V>
decreases csh {
  match c
  case Empty => Empty
  case Bucket(k , h ,_) && k == key => csh
  case Bucket(k , h ,_) && k != key => lookup(csh)
}

// return the first element added to the the cash for key
function method LookupFirst<K(==),V(==)>(csh:Cash<K,V>, key:K) :Option<V>
requires lookup(csh, k) == csh ==> csh
decreases csh {
  match c
  case Empty => Empty
  case Bucket(k , h , Empty) && k != key => Empty
  case Bucket(k , h , rest) && rest !=Empty => LookupFirst(csh, key)
}
// remove any number of entries for a key
function method Purge<K(==),V(==)>(csh:Cash<K,V>, key:K) :Cash<K,V>
decreases csh 
ensures  size(csh) >= size(Purge(csh,key))
//ensures forall kk :: kk !=key ==> isin(csh,kk) // ==> isin(Purge(csh,key),kk)
{
  match c
  case Empty => Empty
  case Bucket(k , h , rest) && k != key => Add(k, h, purge(csh, key))
}

// shorten all histories to be of length 1///
function method Clean<K(==),V(==)>(csh:Cash<K,V>) :Cash<K,V>
decreases csh {
  match csh
  case Empty => Empty
  case Bucket(k , h , rest) && |h| == 1 => csh
  case Bucket(k , h , rest) && |h| > 1 => clean(csh))
}
/* true if csh has a bucket with key */
predicate method isin<K(==),V(==)>(csh:Cash<K,V>, key:K) 
{
  Lookup(csh, key) != Empty
}
/* returns a sequenc containing all  the valuse held against a key*/
function method getvs<K(==),V(==)>(csh:Cash<K,V>, key:K, sofar:seq<V>): seq<V>
requires exists k :: Lookup(csh, key) != Empty
decreases csh
{
  match csh
  case Empty => Empty
  case Bucket(k , h , rest) && k == key => [h[|h|-1], getvs(csh))]
}
/*  are two sequences of values equal*/
predicate method equVals<V(==)>(v1:seq<V>,v2:seq<V>) 
{
  |v1+v2| == |v1| + |v1| && forall i:nat :: 0<=i<|v1| ==> v1[i] == v2[i]
}
/* compute when two cashes have the same history for the same keys.  */ 
predicate method EquCash<K(==),V(==)> (c1:Cash<K,V>, c2:Cash<K,V>)
requires 
decreases c1
{
  match c1
  case Empty => true; 
  case Bucket(k, h, rest) && lookup(k, h)  => EquCash(c1, c2)
  case lookup(k, h) == Empty  => false; 

}
///////////////////////////
////  Your definitions should pass the following test
//////////////////////////
lemma  {:induction cin} dstr_verf<K,V>(cin:Cash<K,V>, kin:K, vin:V) 
//NONONO cycle of death // requires wellFormed(cin) == true;
ensures Lookup(Add(kin,vin,cin),kin) == Some(vin);
ensures Lookup(Add(kin,vin,Empty),kin) == LookupFirst(Add(kin,vin,Empty),kin);
{  }

lemma eqv<V> (vs1:seq<V>, vs2:seq<V>) 
requires equVals(vs1, vs2)
ensures |vs1| == |vs2|
ensures forall i:nat :: 0<=i<|vs1| ==> vs1[i] == vs2[i]
{}
lemma eqc<K,V> (cash1:Cash<K,V>, cash2:Cash<K,V>)
requires EquCash(cash1,cash2)
ensures cash1==Empty <==> cash2==Empty
ensures cash1.Bucket? ==> cash2.Bucket? ==>  
       equVals(cash1.history, getvs(cash2, cash1.key,[]))
{}

method Main() {
  var cash1:Cash<nat,char> := Empty;
  var cash2 := Add(1,'a',cash1);
  var cash3 := Add(2,'b',cash2);
  var cash4 := Add(1,'c',cash3);
  var cash3x := cash3;
  //assert EquCash(cash3,cash3x);
  var cash5 := Clean(Add(2,'b',Add(1,'a',cash4)));
  var cash6 := Add(2,'b',cash2);
  print "  cash3= ",cash3 , "\n";
  print "  cash5= ", cash5 , "\n";
  print "  cash6= ", cash6 , "\n";
  //assert EquCash(cash3,cash3);
  print " getvs(cash5,2)= ",getvs(cash5,2,[]) , "\n";
  print " getvs(cash3,2)= ",getvs(cash3,2,[]) , "\n";
  print equVals(getvs(cash5,2,[]),getvs(cash3,2,[])) , "\n";
  //assert equVals(seq52,seq32);
 
  print "cash4 ",cash4 , "\n";
  print Lookup(cash2,1),"\n";
  assert Lookup(cash2,1) == Some('a');
  assert Lookup(cash2,1) == LookupFirst(cash2,1);
  assert Lookup(Add(2,'b',cash2),2) == Some('b');
  assert Lookup(cash4,1) == Some('c');
  assert LookupFirst(cash4,1) == Some('a');
  print "Add(2,'a',Add(1,'a',cash4)) = ",  Add(2,'a',Add(1,'a',cash4)) , "\n";
  print "  cash5= ", cash5 , "\n";
  print "  cash6= ", cash6 , "\n";
  print "Add(2,'a',cash2)= ",Add(2,'a',cash2),"\n";
  print "** ", EquCash(Add(2,'a',cash2),cash5)," **\n";
  
  
}

