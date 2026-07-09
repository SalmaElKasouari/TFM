include "ValuePQ.dfy"
import opened ValuePQ


predicate Sorted(v : seq<real>)
{
  forall i | 0 <= i < |v| - 1 :: v[i] <= v[i + 1]
}

function Values(pq : multiset<Solution>) : multiset<real>
ensures forall i | i in pq :: pq[i] == Values(pq)[i.value]
// {
//   if pq == multiset{} then
//     multiset{}
//   else {
//     var s := pick();
//     Values(pq) + multiset{s.totalValue}
//   }  
// }


method Heapsort(v : array<real>) returns (w : array<real>)
  requires v.Length > 0
  ensures multiset(w[..]) == multiset(v[..]) // el nuevo array w es una permutacion de v
  ensures Sorted(w[..]) // el nuevo array esta ordenado
{  
  var pq := new PriorityQueue();
  var i := 0;

  assume false;

  // Meter valores en la cola
  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant pq.Valid()
    invariant multiset(v[..i]) == Values(pq.Model()) 
    invariant forall j | 0 <= j < i :: (exists k : Solution | k in pq.Model() :: v[j] == k.value)
  {
    var s := new Solution(v[i]);
    pq.Insert(s);
    i := i + 1;
  }

  assume false;

  w := new real[v.Length];
  i := 0;

  // Extracción ordenada
  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant pq.Valid()    
    invariant Sorted(w[..i]) // ya escritos están ordenados    
    invariant multiset(w[..i]) + Values(pq.Model()) == multiset(v[..]) // conservación de elementos    
    invariant forall x,s :: x in w[..i] && s in pq.Model() ==> x <= s.value // todo los objetos de w[..i] son <= que cualquier elemento de la cola
  {
    var m := pq.Min();
    w[i] := m.value;
    pq.DeleteMin();
    i := i + 1;
  }
}

// separar metodo
method BuildPriorityQueue(v: array<real>) returns (pq: PriorityQueue)
  requires v.Length > 0
  ensures pq.Valid()
  ensures Values(pq.Model()) == multiset(v[..])
{
  pq := new PriorityQueue();
  assert pq.IsEmpty();

  var i := 0;
  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant pq.Valid()
    invariant Values(pq.Model()) == multiset(v[..i])
  {
    var s := new Solution(v[i]);
    pq.Insert(s);
    i := i + 1;
  }
}
