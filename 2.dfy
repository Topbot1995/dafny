// this datatype is a representation for sets that makes unions really fast
// a set is a single element, a union of two sets, or just empty. 
//
//
// note that 
//  Singleton("A")
//  Union(Empty,Singleton("A")) 
//  Union(Union(Singleton("A"),Singleton("A")),Singleton("A")) 
// all represent the same set { "A" }
// (see lemma setRepresentation)


datatype UnionSet<T> = Empty | Singleton(elem : T) | Union(l : UnionSet<T>, r : UnionSet<T>) 

//write insert that returns a new set with m inserted
//hint: just paste it onto the front of S - see lemma "insertIsSimple"
function method insert<T(==)>(m : T, s : UnionSet<T>) : ( r : UnionSet<T> )
  
  ensures isMemberOf(m,r)
{
  Union(Singleton(m), s)
}

//write a predicate isMemberOf to test of m is a member of s 
predicate method isMemberOf<T(==)>(m : T, s : UnionSet<T>) 
  
{
  Union(Singleton(m), s) == s
}

// //write a function asSet to convert a UnionSet to a dafny builtin set
function method asSet<T>(s : UnionSet<T>) : set<T> {

  set x:T | Union(y, s) == s && Union(x, y) == y :: x

}

//Write "IsFlat" which checks if a UnionSet is actually "flat"
//a flat unionSet is either Empty
//or a Union of a singleton element and a flat UnionSet 
//that's to say in a flat unionset, every Union has a singleton in it's left field
//and the only singletons are in the left field of a Union
predicate method isFlat<T(==)>(s : UnionSet<T>) {
  s == flatten(s)
}

//*Hard* write flatten which converts any UnionSet to a flat version
//*hard* you will probably need at least one auxiliary method
// function method flatten<T(==)>(s : UnionSet<T>) : ( r : UnionSet<T> ) 
//  ensures isFlat(r) 
//  {
//    UnionSet x:T , y:UnionSet | Union(y, s) == s && Union(x, y) == y :: (x, y)
//  }

function method patch<T(==)>(s : UnionSet<T>, t : UnionSet<T>) : (r : UnionSet<T>) {
  set s , x | Union(Singleton(x), s) == s :: x
}

//write noduplicates which checks if s has no duplicates
predicate method noDuplicates<T(==)>(s : UnionSet<T>) {
  Union(s, s)

}


//////////////////////////////////////////////////////////////////////////////
//you should be able to verify the following lemmas

lemma insertIsSimple<T>(m : T, s : UnionSet<T>) {
  var i := insert(m, s);

  assert i == Union(Singleton(m),s);
  assert isMemberOf(m,i);
}

lemma isMemberOfOK<T>(m : T, s : UnionSet<T>)  {
  assert !isMemberOf(m, Empty);
  assert isMemberOf(m, Singleton(m));
  assert isMemberOf(m, Union(Singleton(m),Empty));
  assert isMemberOf(m, Union(Empty,Singleton(m)));
  assert !isMemberOf(m, Union(Empty,Empty));

  assert isMemberOf(m, insert(m, s));
}


lemma setRepresetation() 
 ensures asSet( Singleton("A") ) 
      == asSet( Union(Empty,Singleton("A")) )
      == asSet( Union(Union(Singleton("A"),Singleton("A")),Singleton("A")) )
      == { "A" }
{}

lemma flattenSet<T>(s : UnionSet<T>)  
  ensures asSet(s) == asSet(flatten(s))
{}

