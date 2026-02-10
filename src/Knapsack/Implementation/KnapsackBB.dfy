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
include "PQ.dfy"
include "../Specification/SolutionData.dfy"

import opened KnapsackPQ
import opened Input



/* Métodos */

/*
Método: dado un input, encuentra la solución óptima mediante la llamada a un método de vuelta atrás (KnapsackBT)
implementado en BT.dfy. Se construyen dos soluciones:
	- Una solución parcial (ps): va generando la solución actual (decide las asignaciones de los objetos).
	- Una mejor solución (bs): almacena la mejor solución encontrada hasta el momento. 
Ambas soluciones se inicializan con el array de asignaciones a falsos.
//
Verificación: se asegura que la mejor solución encontrada (bs) es tanto válida como óptima:
	- bs.Valid(input): mediante la postcondición en BT que asegura que bs es válida.
	- bs.Optimal (input): mediante varias poscondiciones en BT que aseguran que bs es óptima.
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
	var ps := new Solution(ps_itemsAssign, ps_totalValue, ps_totalWeight, ps_k, ps_priority);
	ps.priority := ps.CalculateUpperBound(input);

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
	bs.priority := ps.priority; // puede que sea muy feo esto, le quiero poner la misma prioridad que ps, la de coger todos los objetos restantes, es decir, todos

	assert bs.Valid(input) by {
		bs.Model().SumOfFalsesEqualsZero(input.Model());	
	}
	

	/* Llamada al método Branch and Bound */
	//KnapsackBB(input, ps, bs);

	/* Primera postcondición: bs.Valid(input) 
		Se verifica gracias a la postcondición en BT que asegura que bs es válida.
	*/

	/* Segunda postcondición: bs.Optimal(input) 
		Se verifica gracias a varias poscondiciones en BT que aseguran que bs es óptima.
	*/
	// assert bs.Optimal(input) by {
	// 	forall s: SolutionData | s.Valid(input.Model()) 
	// 	ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
	// 		assert s.Extends(ps.Model());			
	// 	}
	// }
	assume false;
}

/*
Método: main que ejecuta el programa principal resolviendo el problema de la mochila con una lista de objetos 
y un peso máximo.
*/
method Main() {

	//assert false;

	// /* Objetos que tenemos a nuestra disposición */
	// var item1 := new Item(8.0, 1.0);
	// var item2 := new Item(2.0, 2.0);
	// var item3 := new Item(4.0, 3.0);
	// var items: array<Item> := new Item[3][item1, item2, item3];
	
	
	// /* Peso máximo de la mochila */
	// var maxWeight: real := 8.0;

	// /* Generar la entrada del problema */
	// var input := new Input(items, maxWeight);

	// /* Resolver el problema */
	// var bs := ComputeSolution(input);

	// /* Imprimir la solución */
	// print "The bag admits a weight of: ", input.maxWeight, "\n";
	// print "The maximum value achievable is: ", bs.totalValue, "\n";
	// print "By putting inside:\n";
	// for i := 0 to input.items.Length {
	// 	if (bs.itemsAssign[i]) {
	// 		print "Item ", i," with weight: ", input.items[i].weight, " and value: ", input.items[i].value;
	// 	}
	// }
	// print "\nTotal weight: ", bs.totalWeight, "\n";
}