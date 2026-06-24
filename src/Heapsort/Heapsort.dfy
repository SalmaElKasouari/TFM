include "../Knapsack/Implementation/KnapsackPQ.dfy"

import opened KnapsackPQ
import opened Item


predicate Sorted(v : array<real>)
reads  v
{
  forall i | 0 <= i < v.Length - 1 :: v[i] <= v[i + 1]
}

ghost function Values(v: array<real>, n:int): multiset<real>
reads v
requires 0 <= n <= v.Length
{
    multiset(v[0..n])
}

method NewSolution(n : int, value : real) returns (s : Solution)
  requires n > 0
{
  var s_itemsAssign := new bool[n](i => false);
  var s_totalValue := value;
  var s_totalWeight := 0.0;
  var s_k := 0;
  var s_priority := 0.0;
  s := new Solution(s_itemsAssign, s_totalValue, s_totalWeight, s_k, s_priority);
}

method Heapsort(v : array<real>) returns (w : array<real>)
  requires v.Length > 0
  ensures multiset(w[..]) == multiset(v[..]) // el nuevo array w es una permutacion de v como escribir esta postcondicion
  //ensures Sorted(w) // el nuevo array esta ordenado
{
  
  // Crear objetos solucion y meterlos a la cola de prioridad
  var pq := new PriorityQueue();
  var i := 0;
  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant pq.Valid()
    //invariant pq.Model() == Values(v, i)
    invariant forall j | 0 <= j < i :: (exists k : Solution | k in pq.Model() :: v[j] == k.totalValue)
  {
    var sol := NewSolution(10, v[i]); // creamos una solucion con itemsAssign.Length = 10 y totalValue = v[i]
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
  {
    var min := pq.Min();
    w[i] := min.totalValue;
    pq.DeleteMin();
  }

}
