/*---------------------------------------------------------------------------------------------------------------------

Este fichero incluye la resolución del problema de la mochila.

Estructura del fichero:

  Métodos:
 - ComputeSolution: encuentra una solución óptima que resuelve el problema mediante al método algorítmico de vuelta atrás.
  - Main: ejecuta el programa principal y muestra la solución.

---------------------------------------------------------------------------------------------------------------------*/

include "Item.dfy"
include "Input.dfy"
include "KnapsackPQ.dfy"
include "BB.dfy"
include "PQ.dfy"
include "../Specification/SolutionData.dfy"

import opened KnapsackPQ
import opened Input
import opened SolutionData
import opened Item



/* Métodos */

/*
Método: dado una entrada, encuentra la solución óptima mediante la llamada a un método de ramificación y poda (KnapsackBB)
implementado en BB.dfy. Se construyen dos soluciones:
 - Una solución parcial (ps): va generando la solución actual (decide las asignaciones de los objetos).
 - Una mejor solución (bs): almacena la mejor solución encontrada hasta el momento. 
Ambas soluciones se inicializan con el array de asignaciones a falsos.
//
Verificación: se asegura que la mejor solución encontrada (bs) es tanto válida como óptima:
 - bs.Valid(input): mediante la postcondición en Bb que asegura que bs es válida.
 - bs.Optimal (input): mediante varias poscondiciones en Bb que aseguran que bs es óptima.
*/
method ComputeSolution(input: Input) returns (bs: Solution)
  requires input.Valid()
  //ensures bs.Valid(input)
  //ensures bs.Optimal(input)
{
  var n := input.items.Length;

  /* Construimos una solución parcial (ps) */
  var ps_itemsAssign := new bool[n](i => false);
  var ps_totalValue := 0.0;
  var ps_totalWeight := 0.0;
  var ps_k := 0;
  var ps_priority := 0.0;
  var ps := new Solution(ps_itemsAssign, ps_totalValue, ps_totalWeight, ps_k, ps_priority); // primero la creo con 0 y luego la asigno
  ps.priority := CalculateUpperBound(ps_itemsAssign, ps_k, ps_totalValue, input); // la cota superior es selccionar todos los objetos restantes

  assert ps.Partial(input) by {
    assert ps.Model().Partial(input.Model());
    assert ps.IsUpperBound(input);
  }


  /* Construimos una solución mejor (bs) */
  var bs_itemsAssign := new bool[n](i => false);
  var bs_totalValue := 0.0;
  var bs_totalWeight := 0.0;
  var bs_k := n;
  var bs_priority := 0.0;
  bs := new Solution(bs_itemsAssign, bs_totalValue, bs_totalWeight, bs_k, bs_priority);
  bs.priority := ps.priority; // puede que sea muy feo esto, le quiero poner la misma prioridad que ps, la de coger todos los objetos restantes, porque bs es completa y tiene total value = 0, que implica 0 <= ps.priority

  assert bs.Valid(input) by {
    bs.Model().SumOfFalsesEqualsZero(input.Model());
  }

  /* Branch and Bound */

  var pq := new PriorityQueue(); // en la cola tenemos soluciones parciales validas
  pq.Insert(ps);
  assert pq.Valid();

  ghost var pending : set<SolutionData>:= pq.Pending(input); // soluciones alcanzables desde las soluciones que estan en la cola
  ghost var processed : multiset<SolutionData>;

  SolutionData.rootData(input.Model()).AllNodesG(input.Model());

  assert pq.AllPartial(input); // trivial, en pq solo tenemos a ps que sabemos que es Partial
  assert pq.DisjointTrees(input); // trivial, en pq solo tenemos a ps

  while !pq.IsEmpty() && pq.Min().priority > bs.totalValue
    decreases pq.PartialPending(input)
    invariant LoopInvariant(pq, ps, bs, input)
    invariant fresh(pq)
    invariant fresh(pq.arr)
    //invariant pq.Min().Model() !in pq.PartialPending(input)
    //invariant forall sd : SolutionData | !(sd in pq.Pending(input)) :: sd.TotalValue(input.Model().items) <= bs.totalValue // bs es mejor que todas las soluciones que no están en pending
  {
    LoopBody(ps, bs, pq, input);
  }

  /* Primera postcondición: bs.Valid(input) 
   Se verifica gracias a la postcondición en BB que asegura que bs es válida.
  */

  /* Segunda postcondición: bs.Optimal(input) 
   Se verifica gracias a varias poscondiciones en BB que aseguran que bs es óptima.
  */
  // assert bs.Optimal(input) by {
  //   forall s: SolutionData | s.Valid(input.Model())
  //     ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
  //     assert s.Extends(ps.Model());
  //   }
  // }
}

method LoopBody(ps : Solution, bs : Solution, pq : PriorityQueue, input : Input)
  modifies pq, pq.arr
  requires input.Valid()
  requires LoopInvariant(pq, ps, bs, input)
  requires !pq.IsEmpty() && pq.Min().priority > bs.totalValue // condición del bucle
  ensures LoopInvariant(pq, ps, bs, input)
  ensures pq.arr == old(pq.arr) || fresh(pq.arr) // el array es el mismo que el antiguo (iteraciñon anterior) o se acaba de crear (es fresco)
  ensures pq.PartialPending(input) < old(pq.PartialPending(input))
{
  var father := pq.Min();
  pq.DeleteMin();

  assert pq.PartialPending(input) < old(pq.PartialPending(input)) by {
    PriorityQueue.StaticPartialPendingDecreases(old(pq.Model()), old(pq.Min()), input);
  }

  assert pq.AllPartial(input);
  assert pq.DisjointTrees(input);

  assume false;

  var leftSon : Solution := new Solution.CCopy(father);
  leftSon.k := leftSon.k + 1;

  var rightSon : Solution := new Solution.CCopy(father);
  rightSon.k := rightSon.k + 1;
  //assume false;

  pq.Insert(leftSon);  
  pq.Insert(rightSon);

  PriorityQueue.StaticPartialPendingWithSonsDecreases(pq.Model(), father, leftSon, rightSon, input);



  assume false;




}

ghost predicate LoopInvariant(pq: PriorityQueue, ps: Solution, bs: Solution, input: Input)
  reads pq, pq.arr, pq.arr[..]
  reads input, input.items, input.items[..]
  reads ps, ps.itemsAssign
  reads bs, bs.itemsAssign
  reads set i | 0 <= i < pq.arr.Length :: pq.arr[i].itemsAssign
{
  && pq.Valid()
  && input.Valid()
  && ps.Partial(input)
  && bs.Valid(input)
  && pq.AllPartial(input)
  && pq.DisjointTrees(input)
}


/*
Método: cálculo la cota superior de la mejor solución alcanzable. La cota superior consiste en seleccionar todos los objetos restantes.
//
Verificación: usando el lema AllTruesIsUpperBoundForAll.
*/
method CalculateUpperBound(itemsAssign : array<bool>, k : int, totalValue : real, input : Input) returns (upperBound : real)
  requires input.Valid()
  requires 0 <= k <= itemsAssign.Length
  requires 0 <= k <= input.items.Length == itemsAssign.Length
  requires SolutionData(itemsAssign[..], k).TotalValue(input.Model().items) == totalValue
  ensures forall s : SolutionData | && |s.itemsAssign| == |SolutionData(itemsAssign[..], k).itemsAssign|
                                    && s.k == |s.itemsAssign|
                                    && k <= s.k
                                    && s.Extends(SolutionData(itemsAssign[..], k))
                                    && s.Valid(input.Model())
            :: s.TotalValue(input.Model().items) <= upperBound
{
  ghost var ps' := SolutionData(itemsAssign[..], k);
  assert |ps'.itemsAssign| == |itemsAssign[..]|;
  upperBound := totalValue;

  assert upperBound == ps'.TotalValue(input.Model().items);

  for i := k to itemsAssign.Length
    invariant k <= ps'.k <= |ps'.itemsAssign| == |itemsAssign[..]|
    invariant ps'.Extends(SolutionData(itemsAssign[..], k))
    invariant forall j | k <= j < i :: ps'.itemsAssign[j]
    invariant i == ps'.k
    invariant upperBound == ps'.TotalValue(input.Model().items)
  {
    var oldps' := ps';
    ps' := SolutionData(ps'.itemsAssign[ps'.k := true], ps'.k+1);
    upperBound := upperBound + input.items[i].value;
    SolutionData.AddTrueMaintainsSumConsistency(oldps', ps', input.Model());
  }
  SolutionData.AllTruesIsUpperBoundForAll(SolutionData(itemsAssign[..], k), ps', input.Model());
}

/*
Método: main que ejecuta el programa principal resolviendo el problema de la mochila con una lista de objetos 
y un peso máximo.
*/
method Main() {

  /* Objetos que tenemos a nuestra disposición */
  var item1 := new Item(8.0, 1.0);
  var item2 := new Item(2.0, 2.0);
  var item3 := new Item(4.0, 3.0);
  var items: array<Item> := new Item[3][item1, item2, item3];


  /* Peso máximo de la mochila */
  var maxWeight: real := 8.0;

  /* Generar la entrada del problema */
  var input := new Input(items, maxWeight);

  /* Resolver el problema */
  var bs := ComputeSolution(input);

  /* Imprimir la solución */
  print "The bag admits a weight of: ", input.maxWeight, "\n";
  print "The maximum value achievable is: ", bs.totalValue, "\n";
  print "By putting inside:\n";

  assume bs.Valid(input); // esta es una postcondición de ComputeSolution que de momento esta comentada

  for i := 0 to bs.itemsAssign.Length {
    if (bs.itemsAssign[i]) {
      print "Item ", i," with weight: ", input.items[i].weight, " and value: ", input.items[i].value;
    }
  }
  print "\nTotal weight: ", bs.totalWeight, "\n";

}


// Seleccionar el objeto
  // if (father.totalWeight + input.items[leftSon.k].weight <= input.maxWeight) {
  //   leftSon.itemsAssign[leftSon.k] := true;
  //   leftSon.totalWeight := father.totalWeight + input.items[leftSon.k].weight;
  //   leftSon.totalValue := father.totalValue + input.items[leftSon.k].value;
  //   leftSon.priority := father.priority;
  //   if (leftSon.k == leftSon.itemsAssign.Length) {
  //     bs.Copy(ps);
  //   }
  //   else {
  //     pq.Insert(leftSon);
  //   }
  // }



  // rightSon.itemsAssign[rightSon.k] := false;
  // rightSon.totalWeight := father.totalWeight;
  // rightSon.totalValue := father.totalValue;
  // rightSon.priority := CalculateUpperBound(rightSon.itemsAssign, rightSon.k, rightSon.totalValue, input);
  // if (rightSon.priority > bs.totalValue) {
  //   if (rightSon.k == rightSon.itemsAssign.Length) {
  //     bs.Copy(ps);
  //   }
  //   else {
  //     pq.Insert(rightSon);
  //   }
  // }


  // todos los hijos estan partialPending
  //assert forall s : SolutionData | s.Partial(input.Model()) && s in father.Model().PartialExtensions() :: s in pq.PartialPending(input);

  // father no esta en partialPending
  //assert father.Model() !in pq.PartialPending(input);