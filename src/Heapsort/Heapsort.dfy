include "ValuePQ.dfy"
import opened ValuePQ

/* Predicado: comprueba que una secuencia este ordenada en orden creciente. */
predicate Sorted(v : seq<real>)
{
  forall i | 0 <= i < |v| - 1 :: v[i] <= v[i + 1]
}


lemma OneMoreSorted(v : seq<real>,e:real)
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

lemma AddOne(m : multiset<Solution>,s:Solution)
  requires s !in m
  ensures if s.value !in  Values(m) then
            Values(m+multiset{s}) == Values(m)[s.value:=1]
          else Values(m+multiset{s}) == Values(m)[s.value:=Values(m)[s.value]+1]
  ensures Values(m+multiset{s}).Keys == Values(m).Keys+{s.value}
{
  if s.value !in  Values(m) {
    var ms := m+multiset{s};
    assert Values(ms) == map x | x in (set s <- ms :: s.value) :: |(set ss <- ms  | ss.value == x)|;
    //assert Values(m+multiset{s}).Keys == Values(m).Keys + {s.value};
    //assert Values(m+multiset{s}).Keys == Values(m)[s.value:=1].Keys;
    forall e | e in Values(m+multiset{s})
      ensures Values(m+multiset{s})[e] == Values(m)[s.value:=1][e]
    {
      if (e == s.value) { 
        assert (set ss <-ms  | ss.value == s.value) == {s};
      }
      else {
        assert (set ss <-ms  | ss.value == e) == (set ss <-m  | ss.value == e);
      }

    }
  }
  else { //s.value in Values(m)
    var ms := m + multiset{s};
    assert Values(ms) == map x | x in (set s <- ms :: s.value) :: |(set ss <-ms  | ss.value == x)|;
    //assert Values(m+multiset{s}).Keys == Values(m)[s.value:=Values(m)[s.value]+1].Keys;
    forall e | e in Values(m+multiset{s})
      ensures Values(m+multiset{s})[e] == Values(m)[s.value:=Values(m)[s.value]+1][e]
    {
      if (e == s.value) {
        assert (set ss <-ms  | ss.value == s.value) == (set ss <-m  | ss.value == s.value) + {s};
        //assert |(set ss <-ms  | ss.value == s.value)| == |(set ss <-m  | ss.value == s.value)| + 1;
        assert Values(m+multiset{s})[s.value] == Values(m)[s.value]+1;
      }
      else {
        assert (set ss <-ms  | ss.value == e) == (set ss <-m  | ss.value == e);
      }
    }
  }
}


lemma AddValues(m : multiset<Solution>,s:Solution)
  requires s !in m
  ensures if s.value !in  Values(m) then Values(m+multiset{s})[s.value] == 1
          else  Values(m+multiset{s})[s.value] ==  Values(m)[s.value] + 1
  ensures forall e | e in Values(m) && e != s.value ::  Values(m+multiset{s})[e] ==  Values(m)[e]
{
  AddOne(m,s);
}

ghost predicate SameValues(v : array<real>,pq:PriorityQueue, i:int)
  reads v, pq, pq.arr, set i | 0 <= i < pq.arr.Length :: pq.arr[i]
  requires 0 <= i <= v.Length
  requires pq.Valid()
  requires multiset{pq} !! multiset{pq.arr as object}  !! pq.Model()
{
  && (forall e | e in multiset(v[..i]) :: e in Values(pq.Model())
                                          && multiset(v[..i])[e] == Values(pq.Model())[e])
  && (forall e | e in Values(pq.Model()) :: e in multiset(v[..i]))
  && Values(pq.Model()).Keys == set x <- v[..i]
}

method FillPQ(v : array<real>) returns(pq:PriorityQueue)
  ensures fresh(pq) && fresh(pq.arr)
  ensures pq.Valid() && |pq.Model()| == v.Length ==|v[..]|
  ensures SameValues(v,pq,v.Length)
{
  pq := new PriorityQueue();
  var i := 0;

  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant fresh(pq) && fresh(pq.arr)
    invariant pq.Valid()
    invariant SameValues(v,pq,i)
    invariant |pq.Model()| == i
  {
    var s := new Solution(v[i]);
    ghost var oldpqModel := pq.Model();

    AddValues(pq.Model(),s);
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



method {:only} ExtractPQ(v:array<real>,pq:PriorityQueue) returns (w:array<real>)
  modifies pq,pq.arr
  requires pq.Valid()
  requires |pq.Model()| == v.Length
  requires SameValues(v,pq,v.Length)
  ensures pq.Valid() && pq.IsEmpty() && |pq.Model()| == 0
  ensures fresh(w) && w.Length == v.Length
  ensures Sorted(w[..]) // el nuevo array esta ordenado
{
  w := new real[v.Length];
  assert |pq.Model()| == v.Length == w.Length;
  var i := 0;

  assert multiset(w[..i]) == multiset{};

  while i < w.Length
    decreases w.Length - i
    invariant 0 <= i <= v.Length == w.Length
    invariant pq.Valid()
    invariant |pq.Model()| + i == w.Length
    invariant fresh(w)
    invariant pq.arr == old(pq.arr) || fresh(pq.arr)
    invariant multiset{pq} !! multiset{pq.arr as object} !! multiset{w} !! pq.Model()
    invariant Sorted(w[..i])
    invariant forall e,e' | e in w[..i] && e' in Values(pq.Model()) :: e <= e'
  { 

    var m := pq.Min();

    assert forall e | e in Values(pq.Model()) :: m.value <= e;
    assert m.value in Values(pq.Model());
    assert forall e | e in   w[..i]:: e <= m.value;

    w[i] := m.value;

    assert w[..i+1] == w[..i] + [w[i]];
    assert forall e | e in Values(pq.Model()) :: w[i] <= e;
    assert Sorted(w[..i+1]) by{
      OneMoreSorted(w[..i],w[i]);
    }

    pq.DeleteMin();

    assert forall e,e' | e in w[..i+1] && e' in Values(pq.Model()) :: e <= e';

    i := i + 1;

  }
}


method Heapsort(v : array<real>) returns (w : array<real>)
  ensures Sorted(w[..]) // el nuevo array esta ordenado
{
  var pq := FillPQ(v);
  w := ExtractPQ(v,pq);
}



