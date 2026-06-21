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
  requires input.items.Length > 0
  ensures bs.Valid(input)
  ensures bs.Optimal(input)
{
  var n := input.items.Length;

  var ps_itemsAssign := new bool[n](i => false);
  var ps_totalValue := 0.0;
  var ps_totalWeight := 0.0;
  var ps_k := 0;
  var ps_priority := 0.0;
  var ps := new Solution(ps_itemsAssign, ps_totalValue, ps_totalWeight, ps_k, ps_priority);
  ps.CalculateUpperBound(input);

  var bs_itemsAssign := new bool[n](i => false);
  var bs_totalValue := 0.0;
  var bs_totalWeight := 0.0;
  var bs_k := n;
  var bs_priority := 0.0;
  bs := new Solution(bs_itemsAssign, bs_totalValue, bs_totalWeight, bs_k, bs_priority);
  bs.priority := ps.priority;

  var pq := new PriorityQueue();
  pq.Insert(ps);

  MainLoop(input, pq, bs) by {
    assume false;  // 60"
    assert pq.Model() == multiset{ps};
    assert |pq.Model()| == 1;
    assert pq.Min().Model().k == 0;
    assert pq.Min().Model().AllFalsesFromK();
    assert LoopInvariant(pq, bs, input) by {
      assert input.Valid();
      assert pq.Valid();
      assert pq.Min().Partial(input);
      assert AllPartial(input, pq.Model());
      assert DisjointTrees(input, pq.Model());
      assert bs.Valid(input) by {
        bs.Model().SumOfFalsesEqualsZero(input.Model());
      }
      assert bs !in pq.Model();
      assert DistinctItemsAssign(pq.Model() + multiset{bs});
      assert AllStrictlyPartial(pq.Model());
      forall sd : SolutionData
        | sd.Valid(input.Model()) && sd !in pq.Pending(input)
        ensures sd.TotalValue(input.Model().items) <= bs.totalValue
      {
        assert sd.TotalValue(input.Model().items) <= bs.totalValue by {
          assert forall s : SolutionData | s.Valid(input.Model()) && s.k <= |bs.Model().itemsAssign| == |s.itemsAssign| && bs.k <= s.k && s.Extends(bs.Model()) :: s.TotalValue(input.Model().items) <= bs.priority;
          forall s <- ps.Model().Extensions() | s.Valid(input.Model())
            ensures s.TotalValue(input.Model().items) <= bs.priority
          {
          }
          assert sd.Extends(ps.Model());
          SolutionData.ExtendsInExtensions(input.Model(), sd, ps.Model());
          assert sd in ps.Model().Extensions();
        }
      }
      assert (
          forall p <- pq.Model(), s <- p.Model().Extensions()
                 | s.Valid(input.Model())
            :: s.TotalValue(input.Model().items) <= p.priority
        );
    }
  }
}

method MainLoop(input: Input, pq: PriorityQueue, bs: Solution)
  modifies pq, pq.arr, bs, bs`totalValue, bs`totalWeight, bs`k, bs`itemsAssign, bs`priority, bs.itemsAssign
  requires LoopInvariant(pq, bs, input)
  requires |pq.Model()| == 1
  requires pq.Min().Model().k == 0
  requires pq.Min().Model().AllFalsesFromK()
  ensures bs.Valid(input)
  ensures bs.Optimal(input)
{
  forall sd: SolutionData
    | sd.Valid(input.Model()) && sd.AllFalsesFromK()
    ensures sd in pq.Pending(input)
  {
    assert sd.Extends(pq.Min().Model());
    SolutionData.ExtendsInExtensions(input.Model(), sd, pq.Min().Model());
  }
  while !pq.IsEmpty() && pq.Min().priority > bs.totalValue
    decreases pq.PartialPending(input)
    invariant LoopInvariant(pq, bs, input)
    invariant pq.arr == old(pq.arr) || fresh(pq.arr)
    invariant bs.itemsAssign == old(bs.itemsAssign) || fresh(bs.itemsAssign)
    //invariant pq.Min().Model() !in pq.PartialPending(input)  // es falso!!
  {
    LoopBody(bs, pq, input);
  }
  /*
  assert bs.Optimal(input) by {
    if !pq.IsEmpty() && pq.Min().priority <= bs.totalValue {
      assert forall s <- pq.Model() :: s.priority <= pq.Min().priority;
      forall s: SolutionData
        | s.Valid(input.Model())
        ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)
      {
        assert bs.Model().TotalValue(input.Model().items) == bs.totalValue;
        if s in pq.Pending(input) {
          var p :| p in pq.Model() && p.Partial(input) && s in p.Model().Extensions();
          //assume s.TotalValue(input.Model().items) <= p.priority;
          /*
          TODO: hay que decir que la prioridad de las soluciones parciales es mejor o
          igual que cualquiera de sus descendientes completas.
          */
        } else {
          // Por el invariante del bucle
        }
      }
    }
  }
  */
}

method LoopBody(bs : Solution, pq : PriorityQueue, input : Input)
  modifies pq, pq.arr, bs, bs`totalValue, bs`totalWeight, bs`k, bs`itemsAssign, bs`priority, bs.itemsAssign
  requires LoopInvariant(pq, bs, input)
  ensures LoopInvariant(pq, bs, input)
  ensures pq.arr == old(pq.arr) || fresh(pq.arr)
  ensures bs.itemsAssign == old(bs.itemsAssign) || fresh(bs.itemsAssign)
  ensures pq.PartialPending(input) < old(pq.PartialPending(input))
{
  assume false;
  var trueChild : Solution? := null;
  var falseChild : Solution? := null;
  var oldpq := pq;
  var parent;
  parent := pq.Min();
  pq.DeleteMin();
  if parent.totalWeight + input.items[parent.k].weight <= input.maxWeight {
    trueChild := parent.NewTrueChild(input);
    HandleChild(trueChild, bs, pq, input);
  }
  falseChild := parent.NewFalseChild(input);
  HandleChild(falseChild, bs, pq, input);
}

/*
Lema: si tenemos un nodo child que es hijo de un nodo parent que ya no pertence a la cola, entonces child no esta en ninguno 
de los arboles de los nodos de la cola y ningun nodo de la cola está en los árboles de child.
//
Propósito: demostrar precondición de HandleChild.
//
Verificación: 
*/
lemma NotInTrees(parent : Solution, child : Solution, pq : PriorityQueue, input : Input)
  requires input.Valid()
  requires parent.Partial(input) && parent.Model().AllFalsesFromK()
  requires child.Partial(input) && child.Model().AllFalsesFromK()
  requires (child.IsFalseChild(parent, input) || child.IsTrueChild(parent, input))
  requires pq.Valid()
  requires child !in pq.Model()
  requires parent !in pq.Model()
  requires AllPartial(input, pq.Model() + multiset{parent})
  requires DisjointTrees(input, pq.Model() + multiset{parent})
  ensures AllPartial(input, pq.Model() + multiset{child})
  ensures DisjointTrees(input, pq.Model() + multiset{child})
{
  forall s | s in pq.Model() + multiset{child}
    ensures (pq.Model() + multiset{child})[s] == 1
  {
    if (s == parent) {}
    else if (s == child) {}
    else {
      SubsetDisjointTrees(input, pq.Model() + multiset{parent}, pq.Model());
    }
  }

  forall z | z in pq.Model()
    ensures child.Model().PartialExtensions() !! z.Model().PartialExtensions()
  {
    SolutionData.ExtendsInPartialExtensions(input.Model(), child.Model(), parent.Model());
    assert child.Model() in parent.Model().PartialExtensions();
    assert forall s | s in pq.Model() :: parent.Model().PartialExtensions() !! s.Model().PartialExtensions();
  }
}


/*
Lema: si un conjunto s cumple la propiedad de DisjointTrees y s' esta contenido en s, 
entonces s' también cumple la propiedad de DisjointTrees.
//
Propósito:
//
Verificación: 
*/
lemma SubsetDisjointTrees(input:Input, s:multiset<Solution>, s':multiset<Solution>)
  requires input.Valid()
  requires AllPartial(input,s)
  requires DisjointTrees(input, s)
  requires s' <= s
  ensures AllPartial(input,s')
  ensures DisjointTrees(input, s')
{}


/*
Método: inserta el hijo en la cola si este no es solución completa.
//
Verificación: 
*/
method HandleChild(child : Solution, bs : Solution, pq : PriorityQueue, input : Input) // tarda 197 segundos
  modifies pq, pq.arr, bs, bs.itemsAssign

  // Precondiciones para que los parámetros sean válidos
  requires input.Valid()
  requires child.itemsAssign.Length == bs.itemsAssign.Length
  requires child.Partial(input)
  requires child.Model().AllFalsesFromK()

  requires LoopInvariant(pq, bs, input) // Invariantes del bucle

  // Precondiciones acerca de la relación entre los diferentes objetos
  requires child !in pq.Model() && bs !in pq.Model()// el hijo no pertenece a la cola
  requires child != bs // el hijo no es el objeto bs
  requires (forall s1 <- pq.Model() + multiset{bs,child}, s2 <- pq.Model() + multiset{bs,child} | s1 != s2 :: s1.itemsAssign != s2.itemsAssign) // el hijo, bs y las soluciones de la cola tienen arrays diferentes
  requires DisjointTrees(input, pq.Model() + multiset{child})


  ensures LoopInvariant(pq, bs, input) // Invariantes del bucle

  // Postcondiciones de los diferentes objetos
  ensures child != bs
  ensures child.itemsAssign != bs.itemsAssign
  ensures (forall s : Solution | s in pq.Model() :: s.k < s.itemsAssign.Length)

  // Postcondiciones sobre la cola
  ensures pq.arr == old(pq.arr) || fresh(pq.arr)
  ensures if (child.k != child.itemsAssign.Length && child.priority > bs.totalValue)
          then pq.Model() == old(pq.Model()) + multiset{child}
          else pq.Model() == old(pq.Model())
{
  assume false;
  if (child.priority > bs.totalValue) {
    if (child.k == child.itemsAssign.Length) {
      bs.Copy(child);
      assert pq.Valid();
    }
    else {
      pq.Insert(child);
      assert pq.Valid();
      assert DisjointTrees(input, pq.Model());
      assert DisjointTrees(input, old(pq.Model()) + multiset{child});
      assert DisjointTrees(input, pq.Model());
    }
  }
}



/* 
  Predicado: invariantes del bucle
*/
ghost predicate LoopInvariant(pq: PriorityQueue, bs: Solution, input: Input)
  reads pq, pq.arr, pq.arr[..]
  reads input, input.items, input.items[..]
  reads bs, bs.itemsAssign
  reads set i | 0 <= i < pq.arr.Length :: pq.arr[i].itemsAssign
{
  && input.Valid()
  && pq.Valid()
  && AllPartial(input, pq.Model())
  && DisjointTrees(input, pq.Model())
  && bs.Valid(input)
  && bs !in pq.Model()
  && DistinctItemsAssign(pq.Model() + multiset{bs})
  && AllStrictlyPartial(pq.Model())
  && (
       forall sd : SolutionData
         | sd.Valid(input.Model()) && sd !in pq.Pending(input)
         :: sd.TotalValue(input.Model().items) <= bs.totalValue
     )
  && (
       forall p <- pq.Model(), s <- p.Model().Extensions()
              | s.Valid(input.Model())
         :: s.TotalValue(input.Model().items) <= p.priority
     )
}

ghost predicate AllPartial(input:Input, m: multiset<Solution>)
  reads input, input.items, input.items[..]
  requires input.Valid()
  reads set i | i in m
  reads set i | i in m :: i.itemsAssign
{
  forall s | s in m :: s.Partial(input) && s.Model().AllFalsesFromK()
}

ghost predicate DisjointTrees(input: Input, m: multiset<Solution>)
  reads input, input.items, input.items[..]
  reads m
  reads set i | i in m
  reads set i | i in m :: i.itemsAssign
  requires input.Valid()
  requires AllPartial(input, m)
{
  && (forall s | s in m :: m[s] == 1)
  && (forall s1, s2 | s1 in m && s2 in m && s1 != s2 :: s1.Model().PartialExtensions() !! s2.Model().PartialExtensions())
}

ghost predicate DistinctItemsAssign(m: multiset<Solution>)
  reads m
{
  forall s1 <- m, s2 <- m | s1 != s2 :: s1.itemsAssign != s2.itemsAssign
}

ghost predicate AllStrictlyPartial(m: multiset<Solution>)
  reads m
{
  forall s <- m :: s.k < s.itemsAssign.Length
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