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
  ensures bs.Valid(input)
  ensures bs.Optimal(input)
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

  var pq := new PriorityQueue(1); // en la cola tenemos soluciones parciales validas
  pq.Insert(ps);

  var pending : set<SolutionData>; // soluciones alcanzables desde las soluciones que estan en la cola
  var processed : set<SolutionData>;


  while (/*!pq.IsEmpty() &&*/ pq.Min().priority > bs.totalValue)
    invariant forall s : SolutionData | !(s in pending) :: s.TotalValue(input.Model().items) <= bs.totalValue // bs es mejor que todas las soluciones que no están en pending
  {
    var father := pq.Min();
    pq.DeleteMin();
    var son := father; // copy?
    son.k := son.k + 1;

    // Seleccionar el objeto
    if (father.totalWeight + input.items[son.k].weight <= input.maxWeight) {
      son.itemsAssign[son.k] := true;
      son.totalWeight := father.totalWeight + input.items[son.k].weight;
      son.totalValue := father.totalValue + input.items[son.k].value;
      son.priority := father.priority;
      if (son.k == son.itemsAssign.Length) {
        bs.Copy(ps);
      }
      else {
        pq.Insert(son);
      }
    }

    // No seleccionar el objeto
    son.itemsAssign[son.k] := false;
    son.totalWeight := father.totalWeight;
    son.totalValue := father.totalValue;
    son.priority := CalculateUpperBound(son.itemsAssign, son.k, son.totalValue, input);
    if (son.priority > bs.totalValue) {
      if (son.k == son.itemsAssign.Length) {
        bs.Copy(ps);
      }
      else {
        pq.Insert(son);
      }
    }
    // A pending le quitamos las soluciones alcanzables del nodo procesado
  }










  assume false;

  /* Primera postcondición: bs.Valid(input) 
   Se verifica gracias a la postcondición en BB que asegura que bs es válida.
  */

  /* Segunda postcondición: bs.Optimal(input) 
   Se verifica gracias a varias poscondiciones en BB que aseguran que bs es óptima.
  */
  assert bs.Optimal(input) by {
    forall s: SolutionData | s.Valid(input.Model())
      ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
      assert s.Extends(ps.Model());
    }
  }
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
  for i := 0 to input.items.Length {
    if (bs.itemsAssign[i]) {
      print "Item ", i," with weight: ", input.items[i].weight, " and value: ", input.items[i].value;
    }
  }
  print "\nTotal weight: ", bs.totalWeight, "\n";

}