datatype List<T> = Nil | Cons(car: T, cdr: List<T>)
datatype Option<T> = None | Some(value: T)

//return the second element of a two (or more) element list 
function method second<T>(l: List<T>): T 
    reads *
    decreases list
  { match l    
    case Cons(2,cdr) => cdr
      
  }

//return the second element of of a list, or None if there isn't any
function method secondOpt<T>(l: List<T>): Option<T> 
    reads *
    decreases list
  { match l
    case Nil => None
    case Cons(2,cdr) => cdr      
  }

//return true if the list elements are strictly ascending order
predicate method isPriorityQ(l: List<nat>) 
    reads *
    decreases l
  { match l
    case Nil => true
    case Cons(x, _) => true
    case Cons(d,cdr) => d < Repr(cdr)
  }

//insert n into priroity q, or return the same q if it's already there.
function method insert(n : nat, q : List<nat>): (r : List<nat> )
  reads *
    decreases q
  { match q
    case Nil => r := Nil
    case Cons(x, _) && x > n => r := Cons(n, x) 
    case Cons(x, _) && x == n => r := Cons(x, None) 
    case Cons(d,cdr) && d == n => r := Cons(d,cdr)
    case Cons(d,cdr) && d > n => r := Cons(d, insert(n, cdr))
  }

//return the index of n inside a priority q, or None if it's not there
//you may need an auxiliary function (or not)
function method index(n : nat, q : List<nat>) : (r : Option<nat>) 
    reads *
    decreases q
  { match q
    case Nil => r := None
    case Cons(d, cdr) && d == n => r := 1 + index(n, cdr) 
  }

// Verification test the individual asserted examples in Main
method Main() {
  var l:List<nat> := Cons(1,Cons(2,Cons(3,Nil)));
  assert second(l) == 2;
  assert forall x:List<nat> :: 
                x.Cons? && x.cdr.Cons? ==> second(x) == secondOpt(x).value;
  assert forall x:List<nat> :: 
               x.Nil? || x.cdr.Nil? ==> None == secondOpt(x);

  assert isPriorityQ(l);
  var np:List<nat> := Cons(1,Cons(3,Cons(1,Nil)));
  assert !isPriorityQ(np);
  assert index(1,l).value == 0;  //index from 0
  assert index(3,l).value == 2;
  assert index(0,l) == None;
  var ll:List<nat> := Cons(1,Cons(3,Cons(5,Nil)));
  assert index(4,ll) == None;
 
  assert insert(5,l) == Cons(1,Cons(2,Cons(3,Cons(5,Nil))));
  assert insert(2,l) == Cons(1,Cons(2,Cons(3,Nil)));
  assert insert(2,ll) == insert(5,l);
}

