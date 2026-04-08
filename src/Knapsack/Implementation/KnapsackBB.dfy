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
  ps.priority := ps.CalculateUpperBound(ps_itemsAssign, ps_k, ps_totalValue, input); // la cota superior es seleccionar todos los objetos restantes

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
    invariant LoopInvariant(pq, bs, input)
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
  requires LoopInvariant(pq, bs, input)
  requires !pq.IsEmpty() && pq.Min().priority > bs.totalValue // condición del bucle
  ensures LoopInvariant(pq, bs, input)
  ensures pq.arr == old(pq.arr) || fresh(pq.arr) // el array es el mismo que el antiguo (iteraciñon anterior) o se acaba de crear (es fresco)
  ensures pq.PartialPending(input) < old(pq.PartialPending(input))
{
  var parent := pq.Min();
  pq.DeleteMin();

  assert pq.PartialPending(input) < old(pq.PartialPending(input)) by {
    PriorityQueue.StaticPartialPendingDecreases(old(pq.Model()), old(pq.Min()), input);
  }

  assert pq.AllPartial(input);
  assert pq.DisjointTrees(input);


  var trueChild : Solution? := null;
  var falseChild : Solution? := null;

 

  // if (parent.totalWeight + input.items[parent.k].weight <= input.maxWeight) {
  //   trueChild := parent.NewTrueChild(input);
  //   HandleChild(trueChild, bs, pq, input);
  // }
  assume false;

  falseChild := parent.NewFalseChild(input);
  HandleChild(falseChild, bs, pq, input);

  if (trueChild == null && falseChild == null) {
    // ya sabe que pq decrede por el lema invocado antes: PriorityQueue.StaticPartialPendingDecreases(old(pq.Model()), old(pq.Min()), input);
  }
  // else if (trueChild != null && falseChild == null) {

  // }

  assume false;

}

/*
    Método: inserta el hijo en cola si este no es solución completa.
    //
    Verificación: 
    */
method HandleChild(child : Solution, bs : Solution, pq : PriorityQueue, input : Input)
  modifies pq, pq.arr, bs, bs`totalValue, bs`totalWeight, bs`k, bs`itemsAssign, bs`priority, bs.itemsAssign
  requires child.itemsAssign.Length == bs.itemsAssign.Length
  requires child != bs
  requires input.Valid()
  requires child.Partial(input)
  requires LoopInvariant(pq, bs, input)
  //ensures LoopInvariant(pq, bs, input) //ir trozo por trozo
  ensures child != bs
  ensures bs == old(bs)
  //ensures pq.arr == old(pq.arr) || fresh(pq.arr)
  ensures pq.Valid()
  ensures if (child.k != child.itemsAssign.Length && child.priority > bs.priority)
          then pq.Model() ==  old(pq.Model()) + multiset{child}
          else pq.Model() == old(pq.Model())
{
  if (child.priority > bs.totalValue) {
    if (child.k == child.itemsAssign.Length) {
      bs.Copy(child);
      assert pq.Valid();
    }
    else {
      pq.Insert(child);
      assert pq.Valid();
    }
  }
}

ghost predicate LoopInvariant(pq: PriorityQueue, bs: Solution, input: Input)
  reads pq, pq.arr, pq.arr[..]
  reads input, input.items, input.items[..]
  reads bs, bs.itemsAssign
  reads set i | 0 <= i < pq.arr.Length :: pq.arr[i].itemsAssign
{
  && pq.Valid()
  && input.Valid()
  && bs.Valid(input)
  && pq.AllPartial(input)
  && pq.DisjointTrees(input)
  && bs !in pq.Model()
  && (forall s : Solution | s in pq.Model() :: s.k < s.itemsAssign.Length) // StrictPartial
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
  // if (parent.totalWeight + input.items[trueChild.k].weight <= input.maxWeight) {
  //   trueChild.itemsAssign[trueChild.k] := true;
  //   trueChild.totalWeight := parent.totalWeight + input.items[trueChild.k].weight;
  //   trueChild.totalValue := parent.totalValue + input.items[trueChild.k].value;
  //   trueChild.priority := parent.priority;
  //   if (trueChild.k == trueChild.itemsAssign.Length) {
  //     bs.Copy(ps);
  //   }
  //   else {
  //     pq.Insert(trueChild);
  //   }
  // }



  // falseChild.itemsAssign[falseChild.k] := false;
  // falseChild.totalWeight := parent.totalWeight;
  // falseChild.totalValue := parent.totalValue;
  // falseChild.priority := CalculateUpperBound(falseChild.itemsAssign, falseChild.k, falseChild.totalValue, input);
  // if (falseChild.priority > bs.totalValue) {
  //   if (falseChild.k == falseChild.itemsAssign.Length) {
  //     bs.Copy(ps);
  //   }
  //   else {
  //     pq.Insert(falseChild);
  //   }
  // }


  // todos los hijos estan partialPending
  //assert forall s : SolutionData | s.Partial(input.Model()) && s in parent.Model().PartialExtensions() :: s in pq.PartialPending(input);

  // parent no esta en partialPending
  //assert parent.Model() !in pq.PartialPending(input);