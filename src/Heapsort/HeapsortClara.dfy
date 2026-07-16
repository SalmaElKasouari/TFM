include "ValuePQ.dfy"
import opened ValuePQ


predicate Sorted(v : seq<real>)
{
  forall i | 0 <= i < |v| - 1 :: v[i] <= v[i + 1]
}


lemma oneMoreSorted(v : seq<real>,e:real)
requires Sorted(v)
requires forall x | x in v :: x <= e
ensures Sorted(v+[e])
{ if v ==[]  {}
  else { assert v[|v|-1] in v && v[|v|-1] <= e;}
}

ghost function Values(pq : multiset<Solution>) : map<real,nat>
reads pq
{ 
  map x | x in (set s <- pq :: s.value) :: |(set ss <- pq | ss.value == x)|
 }

lemma addOne(m : multiset<Solution>,s:Solution)
requires s !in m
ensures if s.value !in  Values(m) then 
             Values(m+multiset{s}) == Values(m)[s.value:=1]
        else Values(m+multiset{s}) == Values(m)[s.value:=Values(m)[s.value]+1]
ensures Values(m+multiset{s}).Keys == Values(m).Keys+{s.value}      
{
  if s.value !in  Values(m)
   { var ms := m+multiset{s};
     assert Values(ms) == map x | x in (set s <- ms :: s.value) :: |(set ss <-ms  | ss.value == x)|;
     assert Values(m+multiset{s}).Keys == Values(m).Keys + {s.value};
     assert Values(m+multiset{s}).Keys == Values(m)[s.value:=1].Keys;
     forall e | e in Values(m+multiset{s})
     ensures Values(m+multiset{s})[e] == Values(m)[s.value:=1][e]
     {     
      if (e == s.value)
         { assert (set ss <-ms  | ss.value == s.value) == {s};}
      else {
         assert (set ss <-ms  | ss.value == e) == (set ss <-m  | ss.value == e);
      }   

     }

   }
  else {//s.value in Values(m)
    var ms := m+multiset{s};
     assert Values(ms) == map x | x in (set s <- ms :: s.value) :: |(set ss <-ms  | ss.value == x)|;
     assert Values(m+multiset{s}).Keys == Values(m)[s.value:=Values(m)[s.value]+1].Keys;
     forall e | e in Values(m+multiset{s})
     ensures Values(m+multiset{s})[e] == Values(m)[s.value:=Values(m)[s.value]+1][e]
     {
      if (e == s.value) {
        assert (set ss <-ms  | ss.value == s.value) == (set ss <-m  | ss.value == s.value) + {s};
        assert |(set ss <-ms  | ss.value == s.value)| == |(set ss <-m  | ss.value == s.value)| + 1;
        assert Values(m+multiset{s})[s.value] == Values(m)[s.value]+1;
      }
      else {
        assert (set ss <-ms  | ss.value == e) == (set ss <-m  | ss.value == e);

      }
     }  
  }
}


lemma addValues(m : multiset<Solution>,s:Solution)
requires s !in m
ensures if s.value !in  Values(m) then Values(m+multiset{s})[s.value] == 1
        else  Values(m+multiset{s})[s.value] ==  Values(m)[s.value] + 1
ensures forall e | e in Values(m) && e != s.value ::  Values(m+multiset{s})[e] ==  Values(m)[e]
{
  addOne(m,s);
}



lemma {:axiom} delOne(m : multiset<Solution>,s:Solution)
requires s in m 
ensures s.value in Values(m) && Values(m)[s.value]>0
ensures Values(m-multiset{s}) == Values(m)[s.value:=Values(m)[s.value]-1]
ensures Values(m-multiset{s})[s.value] ==  Values(m)[s.value] - 1
ensures forall e | e in Values(m) && e != s.value ::  Values(m-multiset{s})[e] ==  Values(m)[e]
ensures if Values(m)[s.value]> 1 then Values(m-multiset{s}).Keys == Values(m).Keys
        else Values(m-multiset{s}).Keys == Values(m).Keys-{s.value}




ghost predicate sameValues(v : array<real>,pq:PriorityQueue, i:int)
reads v, pq, pq.arr, set i | 0 <= i < pq.arr.Length :: pq.arr[i]
requires 0 <= i <= v.Length
requires pq.Valid() //&& |pq.Model()| == v.Length
requires multiset{pq} !! multiset{pq.arr as object}  !! pq.Model()
{
  (forall e | e in multiset(v[..i]) :: e in Values(pq.Model()) && multiset(v[..i])[e] == Values(pq.Model())[e]) &&
  (forall e | e in Values(pq.Model()) :: e in multiset(v[..i])) &&
  Values(pq.Model()).Keys == set x <- v[..i]
}


ghost predicate sumValues(v : array<real>,w:array<real>,pq:PriorityQueue, i:int)
reads v, w, pq, pq.arr, set i | 0 <= i < pq.arr.Length :: pq.arr[i]
requires 0 <= i <= v.Length == w.Length
requires pq.Valid() //&& |pq.Model()| == v.Length
requires multiset{pq} !! multiset{pq.arr as object}  !! pq.Model()
{
      (forall e | e in multiset(v[..]) :: (e in multiset(w[..i]) || e in Values(pq.Model())))
   && (forall e | e in multiset(w[..i]) :: e in multiset(v[..]))

   && forall e | e in multiset(v[..]) ::
                 if  e in Values(pq.Model()) && e in multiset(w[..i]) then multiset(v[..])[e] == Values(pq.Model())[e]  + multiset(w[..i])[e]
                 else if e in Values(pq.Model()) && e !in multiset(w[..i]) then  multiset(v[..])[e] == Values(pq.Model())[e] 
                 else multiset(v[..])[e] == multiset(w[..i])[e]

 }


lemma finalValues(v : array<real>,w:array<real>,pq:PriorityQueue)
requires v.Length == w.Length
requires pq.Valid() && |pq.Model()| == 0
requires multiset{pq} !! multiset{pq.arr as object}  !! pq.Model()
requires sumValues(v,w,pq,w.Length)
ensures multiset(w[..]) == multiset(v[..])
{
  assert pq.Model() == multiset{};
  assert Values(pq.Model()).Keys == {};
  assert forall e | e in multiset(v[..]) :: e !in Values(pq.Model()) && e in  multiset(w[..]);

  forall e | e in multiset(v[..]) 
  ensures multiset(v[..])[e] == multiset(w[..])[e]
  { assert e !in Values(pq.Model()) && e in  multiset(w[..]);
    assert multiset(v[..])[e] == multiset(w[..w.Length])[e];
    assert w[..] == w[..w.Length];
  }
  
 //   assert multiset(v[..]) <= multiset(w[..]);
 // assert forall e | e in multiset(w[..]):: e in multiset(v[..]);  
 // assert multiset(w[..]) <= multiset(v[..]);
}




method {:verify false} fillPQ(v : array<real>) returns(pq:PriorityQueue)//41,4s
ensures  fresh(pq) && fresh(pq.arr)
ensures  pq.Valid() && |pq.Model()| == v.Length ==|v[..]|
ensures sameValues(v,pq,v.Length)
{
  pq := new PriorityQueue();
  var i := 0;  

  // Meter valores en la cola
  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant fresh(pq) && fresh(pq.arr)
    invariant pq.Valid()
    invariant sameValues(v,pq,i)
    invariant |pq.Model()| == i
  {
    var s := new Solution(v[i]);
    ghost var oldpqModel := pq.Model();

    addValues(pq.Model(),s);
    assert forall e | e in Values(oldpqModel) && e != s.value ::  Values(oldpqModel+multiset{s})[e] ==  Values(oldpqModel)[e];
    assert s.value !in  Values(oldpqModel) ==> Values(oldpqModel+multiset{s})[s.value] == 1;


    pq.Insert(s);
    assert pq.Model() == oldpqModel + multiset{s};
    assert v[..i+1] == v[..i] + [v[i]];
    assert  multiset(v[..i+1]) == multiset(v[..i]) + multiset{v[i]};
    assert v[i] in Values(pq.Model());

    i := i + 1;
    
  }
  assert v[..i] == v[..];
}


method extractPQ(v:array<real>,pq:PriorityQueue) returns (w:array<real>)//27,7 s
modifies pq,pq.arr
requires  pq.Valid()
requires |pq.Model()| == v.Length
requires sameValues(v,pq,v.Length)
ensures pq.Valid() && pq.IsEmpty() && |pq.Model()| == 0
ensures fresh(w) && w.Length == v.Length
ensures multiset(w[..]) == multiset(v[..]) // el nuevo array w es una permutacion de v
//ensures Sorted(w[..]) // el nuevo array esta ordenado
{
  w := new real[v.Length];
  assert |pq.Model()| == v.Length == w.Length;
  var i := 0;
  // Extracción ordenada

  assert multiset(w[..i]) == multiset{};
      ghost var fullpq := Values(pq.Model());
  assert (v[..v.Length]) == (v[..]);

 // assert forall e | e in multiset(v[..]) :: e in Values(pq.Model()) && e !in multiset(w[..i]) && multiset(v[..])[e] == Values(pq.Model())[e] ;
  while i < w.Length
    decreases w.Length - i
    invariant 0 <= i <= v.Length == w.Length
    invariant pq.Valid()    
    invariant |pq.Model()| + i == w.Length 
    invariant fresh(w) 
    invariant pq.arr == old(pq.arr) || fresh(pq.arr)
    invariant multiset{pq} !! multiset{pq.arr as object} !! multiset{w} !! pq.Model()
    invariant Values(pq.Model()).Keys <= fullpq.Keys 
    //invariant Values(pq.Model()).Keys + (set x <- w[..i]) == fullpq.Keys
    invariant fullpq.Keys == set x <- v[..]

    invariant forall e | e in multiset(v[..]) :: (e in multiset(w[..i]) || e in Values(pq.Model()))
    invariant forall e | e in multiset(w[..i]) :: e in multiset(v[..])

    invariant forall e | e in multiset(v[..]) ::
                 if  e in Values(pq.Model()) && e in multiset(w[..i]) then multiset(v[..])[e] == Values(pq.Model())[e]  + multiset(w[..i])[e]
                 else if e in Values(pq.Model()) && e !in multiset(w[..i]) then  multiset(v[..])[e] == Values(pq.Model())[e] 
                 else multiset(v[..])[e] == multiset(w[..i])[e]
    
    
    //invariant Sorted(w[..i]) // ya escritos están ordenados 
    //invariant forall e,e' | e in w[..i] && e' in Values(pq.Model()) :: e <= e'
  { 
    
    var m := pq.Min();    
    w[i] := m.value;
    
    assert w[..i+1] == w[..i] + [w[i]];

    /*assert forall e | e in Values(pq.Model()) :: m.value <= e;
    assert m.value in Values(pq.Model());
    assert forall e | e in   w[..i]:: e <= m.value; 
    assert forall e | e in Values(pq.Model()) :: w[i] <= e;  
    assert Sorted(w[..i+1]) by{
       oneMoreSorted(w[..i],w[i]);
    }*/

    forall e | e in multiset(w[..i+1]) ensures e in multiset(v[..])
    {
      if e in multiset(w[..i]) {}
      else { assert e == w[i] == m.value;
             assert m.value in fullpq.Keys;
      }
    }


    ghost var oldpqModel := pq.Model();
    assert |oldpqModel| + i == w.Length;
    forall e | e in multiset(v[..]) 
    ensures e in multiset(w[..i+1]) || e in Values(oldpqModel)
    {
      assert e in multiset(w[..i]) || e in Values(oldpqModel);
      if (e !in multiset(w[..i+1])) && (e !in Values(oldpqModel))
      { assert e !in multiset(w[..i]);
        assert false;
      }
    }

    delOne(pq.Model(),m);
    assert forall e | e in Values(oldpqModel) && e != m.value ::  Values(oldpqModel-multiset{m})[e] ==  Values(oldpqModel)[e];
    assert Values(oldpqModel-multiset{m})[m.value] ==  Values(oldpqModel)[m.value]-1;

    pq.DeleteMin();
 
    //assert forall e,e' | e in w[..i+1] && e' in Values(pq.Model()) :: e <= e';
    
    /*forall e | e in multiset(v[..]) 
    ensures (e in multiset(w[..i+1]) || e in Values(pq.Model()))
    { assume false;
    }*/
    /*forall e | e in multiset(v[..]) 
    ensures multiset(v[..])[e] == Values(pq.Model())[e]  + multiset(w[..i])[e]
    {assume false;}*/

    /*forall e | e in multiset(v[..]) ensures
                 if  e in Values(pq.Model()) && e in multiset(w[..i+1]) then multiset(v[..])[e] == Values(pq.Model())[e]  + multiset(w[..i+1])[e]
                 else if e in Values(pq.Model()) && e !in multiset(w[..i+1]) then  multiset(v[..])[e] == Values(pq.Model())[e] 
                 else multiset(v[..])[e] == multiset(w[..i+1])[e]
    {assume false;}*/
    assert |pq.Model()| == |oldpqModel| - 1;
    assert |pq.Model()| + (i+1) == |oldpqModel| + i == w.Length; 

    /*forall e | e in multiset(v[..])  ensures
      if  e in Values(pq.Model()) && e in multiset(w[..i+1]) then multiset(v[..])[e] == Values(pq.Model())[e]  + multiset(w[..i+1])[e]
      else if e in Values(pq.Model()) && e !in multiset(w[..i+1]) then  multiset(v[..])[e] == Values(pq.Model())[e] 
      else multiset(v[..])[e] == multiset(w[..i+1])[e]{
       if (e != w[i]) {}
       else if e !in Values(oldpqModel) 
         {assert e != w[i] && e !in Values(pq.Model());
          assert multiset(w[..i+1])[e] == multiset(w[..i])[e];
          assert multiset(v[..])[e] == multiset(w[..i])[e];
          }
        else //e == w[i] && e in Values(oldpqModel) 
        {
         if e in Values(pq.Model()) {
          assert Values(pq.Model())[e] == Values(oldpqModel)[e]-1;
          assert multiset(w[..i+1])[e] == multiset(w[..i])[e] + 1;
          //la suma total no ha cambiado
         }
         else {//era la ultima aparicion en la cola
          if e in multiset(w[..i])
           {assert  Values(oldpqModel)[e] == 1;
            assert multiset(v[..])[e] == multiset(w[..i])[e]+ 1; }
          else{
            assert multiset(v[..])[e] == 1;
          }  
         }

        }*/


      //assume false;  
    //}      
    i := i + 1;
    assume false;
  }
  //Una vez consumida la cola de prioridad, todos los elementos están en w, con la misma
  //multiplicidad que en v
  //Ademas, w está ordenado
  assert |pq.Model()| == 0;

  finalValues(v,w,pq);
}


method {:verify false} Heapsort(v : array<real>) returns (w : array<real>)
  ensures multiset(w[..]) == multiset(v[..]) // el nuevo array w es una permutacion de v
  ensures Sorted(w[..]) // el nuevo array esta ordenado
{  
  var pq := fillPQ(v);
  w := extractPQ(v,pq);
}

  


