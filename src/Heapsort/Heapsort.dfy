include "ValuePQ.dfy"

import opened ValuePQ


predicate Sorted(v : seq<real>)
{
  forall i | 0 <= i < |v| - 1 :: v[i] <= v[i + 1]
}

// ghost function Values(v: array<real>, n:int): multiset<real>
// reads v
// requires 0 <= n <= v.Length
// {
//   multiset(v[0..n])
// }

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

method hola(pq : PriorityQueue, sol : Solution)
modifies pq
{
 pq.Insert(sol);
}


method Heapsort(v : array<real>) returns (w : array<real>)
  requires v.Length > 0
  ensures multiset(w[..]) == multiset(v[..]) // el nuevo array w es una permutacion de v como escribir esta postcondicion
  //ensures Sorted(w) // el nuevo array esta ordenado
{
  
  // Crear objetos solucion y meterlos a la cola de prioridad
  var pq := new PriorityQueue();
  assert pq.Valid();
  //assume false;
  var i := 0;
  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant pq.Valid()
    invariant Values(pq.Model()) == multiset(v[..i])
    //invariant pq.Model() == Values(v, i)
    //invariant forall j | 0 <= j < i :: (exists k : Solution | k in pq.Model() :: v[j] == k.totalValue)
  {
    var sol := new Solution(v[i]); // creamos una solucion con itemsAssign.Length = 10 y totalValue = v[i]
    assume pq.Valid();
    pq.Insert(sol);
    i := i + 1;
  }
  assume false;

  // Sacamos los objetos de la cola y los metemos en w
  i := 0;
  w := new real [v.Length];
  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant pq.Valid()
    invariant Sorted(w[..i])
    //los que estan en w..i son  o iguales que los que estan en la cola
  {
    var min := pq.Min();
    w[i] := min.value;
    pq.DeleteMin();
  }

}
