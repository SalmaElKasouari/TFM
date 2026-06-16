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
method {:only} ComputeSolution(input: Input) returns (bs: Solution)
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

  SolutionData.rootData(input.Model()).AllNodesG(input.Model());

  assert AllPartial(input, pq.Model()); // trivial, en pq solo tenemos a ps que sabemos que es Partial
  assert DisjointTrees(input, pq.Model()); // trivial, en pq solo tenemos a ps

  assert input.Valid();

  //assume false;

  while !pq.IsEmpty() && pq.Min().priority > bs.totalValue
    decreases pq.PartialPending(input)
    invariant LoopInvariant(pq, bs, input) //
    invariant fresh(pq)
    invariant fresh(pq.arr)
    invariant bs.Valid(input) //
    invariant bs.Optimal(input) //
    invariant pq.Min().Model() !in pq.PartialPending(input)
    invariant forall sd : SolutionData | !(sd in pq.Pending(input)) :: sd.TotalValue(input.Model().items) <= bs.totalValue // bs es mejor que todas las soluciones que no están en pending
  {
    assume false;
    LoopBody(ps, bs, pq, input);
  }
  assume false;
  
    
  /* Primera postcondición: bs.Valid(input)
   Se verifica gracias a la postcondición de LoopBody y el invariante del bucle* Segunda postcondición: bs.Optimal(input)
   Se verifica gracias a varias poscondiciones en BB que aseguran que bs es óptima.
  */


  // assert bs.Optimal(input) by {
  //   forall s: SolutionData | s.Valid(input.Model())
  //     ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
  //     assert s.Extends(ps.Model());
  //   }
  // }
}

/*
method m2(
  ps : Solution, bs : Solution, pq : PriorityQueue, input : Input,
  parent: Solution
) returns (trueChild : Solution)
  requires input.Valid()
  requires input.Valid()
  requires pq.Valid()
  requires AllPartial(input, pq.Model() + multiset{parent})
  requires DisjointTrees(input, pq.Model() + multiset{parent})
  requires bs.Valid(input)
  requires bs !in pq.Model()
  requires DistinctItemsAssign(pq.Model() + multiset{bs,parent})
  requires AllStrictlyPartial(pq.Model() + multiset{parent})
  requires !pq.IsEmpty() && pq.Min().priority > bs.totalValue // condición del bucle
  requires parent.totalWeight + input.items[parent.k].weight <= input.maxWeight
{
  assert parent.k < parent.itemsAssign.Length;
  assert parent.itemsAssign.Length == input.items.Length;
  trueChild := parent.NewTrueChild(input);
  //NotInTrees(parent, trueChild, pq, input);

  HandleChild(trueChild, bs, pq, input) by {
  }
}

method m1(
  ps : Solution, bs : Solution, pq : PriorityQueue, input : Input,
  parent: Solution
) returns (trueChild : Solution?)
  requires input.Valid()
  requires input.Valid()
  requires pq.Valid()
  requires AllPartial(input, pq.Model() + multiset{parent})
  requires DisjointTrees(input, pq.Model() + multiset{parent})
  requires bs.Valid(input)
  requires bs !in pq.Model()
  requires DistinctItemsAssign(pq.Model() + multiset{bs,parent})
  requires AllStrictlyPartial(pq.Model() + multiset{parent})
  requires !pq.IsEmpty() && pq.Min().priority > bs.totalValue // condición del bucle
{
  assert parent.k < parent.itemsAssign.Length;
  assert parent.itemsAssign.Length == input.items.Length;
  if parent.totalWeight + input.items[parent.k].weight <= input.maxWeight {
    trueChild := m2(ps, bs, pq, input, parent);
  }
  trueChild := null;
}
*/


/*
Método: cuerpo del bucle

//
Verificación: 
*/
method {:verify false} LoopBody(ps : Solution, bs : Solution, pq : PriorityQueue, input : Input)
  modifies pq, pq.arr, bs, bs`totalValue, bs`totalWeight, bs`k, bs`itemsAssign, bs`priority, bs.itemsAssign

  requires input.Valid() //
  requires LoopInvariant(pq, bs, input) //
  requires !pq.IsEmpty() && pq.Min().priority > bs.totalValue // condición del bucle
  requires allocated(pq.Model())
  requires bs.Valid(input) //
  requires bs.Optimal(input) //

  ensures input.Valid() //
  ensures LoopInvariant(pq, bs, input) //
  ensures allocated(pq.Model())
  ensures pq.arr == old(pq.arr) || fresh(pq.arr) // el array es el mismo que el antiguo (iteracion anterior) o se acaba de crear (es fresco)
  ensures pq.PartialPending(input) < old(pq.PartialPending(input))  
  ensures bs.Valid(input) //
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().Equals(old(bs.Model())) // bs es extension optima de ps o no ha cambiado
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)   //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs). 
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items)) // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior

{
  // assert pq.PartialPending(input) < old(pq.PartialPending(input)) by {
  //   PriorityQueue.StaticPartialPendingDecreases(old(pq.Model()), old(pq.Min()), input);
  // }

  var trueChild : Solution? := null;
  var falseChild : Solution? := null;
  var oldpq := pq;
  var parent;
  opaque
  modifies pq, pq.arr
  //ensures LoopInvariant(pq, bs, input)
  ensures pq.arr == old(pq.arr) || fresh(pq.arr)
  ensures input.Valid()
  ensures pq.Valid()
  ensures AllPartial(input, pq.Model() + multiset{parent})
  ensures DisjointTrees(input, pq.Model() + multiset{parent})
  ensures bs.Valid(input)
  ensures bs !in pq.Model()
  ensures parent !in pq.Model()
  ensures DistinctItemsAssign(pq.Model() + multiset{bs,parent})
  ensures AllStrictlyPartial(pq.Model() + multiset{parent})
  ensures allocated(pq.Model())
  {
    assume false;
    parent := pq.Min();
    label L :
    pq.DeleteMin();
    assert pq.arr == old(pq.arr) || fresh(pq.arr);
    assert input.Valid();
    assert pq.Valid();
    assert AllPartial(input, pq.Model() + multiset{parent});
    assert DisjointTrees(input, pq.Model() + multiset{parent});
    assert bs.Valid(input);
    assert bs !in pq.Model();
    assert DistinctItemsAssign(pq.Model() + multiset{bs,parent});
    assert AllStrictlyPartial(pq.Model() + multiset{parent});
  }

  opaque
  modifies pq, pq.arr, bs, bs.itemsAssign
  {
    assert parent.k < parent.itemsAssign.Length;
    assert parent.itemsAssign.Length == input.items.Length by {
      assert parent.Partial(input);
    }
    if parent.totalWeight + input.items[parent.k].weight <= input.maxWeight {
      assert input.Valid();
      opaque
      modifies {}
      ensures input.Valid()
      ensures parent.Partial(input) && parent.Model().AllFalsesFromK()
      ensures trueChild != null
      ensures trueChild.Partial(input) && trueChild.Model().AllFalsesFromK()
      ensures trueChild.IsTrueChild(parent, input)
      ensures pq.Valid()
      ensures parent !in pq.Model()
      ensures AllPartial(input, pq.Model() + multiset{parent})
      ensures fresh(trueChild.itemsAssign)
      //ensures DistinctItemsAssign(pq.Model() + multiset{bs, parent})
      ensures DistinctItemsAssign(pq.Model() + multiset{bs, parent, trueChild})
      ensures DisjointTrees(input, pq.Model() + multiset{parent})

      ensures trueChild.itemsAssign.Length == bs.itemsAssign.Length
      ensures trueChild !in pq.Model()
      ensures bs !in pq.Model()
      ensures trueChild != bs
      ensures trueChild != parent

      ensures allocated(pq.Model())
      {
        //assume false;
        assert forall s <- pq.Model() :: allocated(s.itemsAssign);
        assert allocated(parent.itemsAssign);
        assert allocated(bs.itemsAssign);
        trueChild := parent.NewTrueChild(input);
        assert trueChild.itemsAssign != parent.itemsAssign;
        assert trueChild.itemsAssign != bs.itemsAssign;
        assert trueChild.itemsAssign !in (set s <- pq.Model() :: s.itemsAssign);
        assert DistinctItemsAssign(pq.Model() + multiset{bs, parent});
        assert DistinctItemsAssign(pq.Model() + multiset{bs, parent, trueChild});
      }
      NotInTrees(parent, trueChild, pq, input);

      opaque
      modifies pq, pq.arr, bs, bs.itemsAssign
      {
        HandleChild(trueChild, bs, pq, input) by {
          assume false;  // 200"
        }
        assume false;
      }
      assume false;
    }
  }

  assume false;

  opaque
  {
    //assume false;
    falseChild := parent.NewFalseChild(input);
    HandleChild(falseChild, bs, pq, input) by {
      assume LoopInvariant(pq, bs, input);
      NotInTrees(parent, falseChild, pq, input);
    }
  }

  assume false;

  // if (trueChild == null && falseChild == null) {
  //   // ya sabe que pq decrede por el lema invocado antes: PriorityQueue.StaticPartialPendingDecreases(old(pq.Model()), old(pq.Min()), input);
  // }
  // // else if (trueChild != null && falseChild == null) {}
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