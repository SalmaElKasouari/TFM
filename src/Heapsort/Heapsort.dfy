include "../Knapsack/Implementation/KnapsackPQ.dfy"

import opened KnapsackPQ
import opened Item

function Set(v : seq<real>) : set<real>
{
    set i | 0 <= i < |v| :: v[i]
}

predicate Sorted(v : array<real>)
reads  v
{
    forall i | 0 <= i < v.Length - 1 :: v[i] <= v[i + 1]
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

method Heasort(v : array<real>) returns (w : array<real>)
requires v.Length > 0
//ensures Set(v[..]) == Set(w[..]) // el nuevo array w es una permutacion de v
//ensures Sorted(w) // el nuevo array esta ordenado
{
    w := new real [v.Length];
    var pq := new PriorityQueue();
    var i := 0;

    // Crear objetos solucion y meterlos a la cola de prioridad
    while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant pq.Valid()
    invariant |pq.Model()| == i
    //invariant |Set(v[..i])| == |pq.Model()|
    {        
        assume false;
        var sol := NewSolution(10, v[i]); // creamos una solucion con itemsAssign.Length = 10 y totalValue = v[i]
        pq.Insert(sol);
        i := i + 1;
    }
    assume false;

    // Sacamos los objetos de la cola y los metemos en w
    i := 0;
    while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant pq.Valid()
    {   
        //assume false;
        w[i] := pq.Min().totalValue;
        i := i + 1;
    }

}
