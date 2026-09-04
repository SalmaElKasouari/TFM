/*---------------------------------------------------------------------------------------------------------------------

Este fichero incluye la resolución del problema de la mochila.

Estructura del fichero:

  Predicados:
  - SameSizeItemsAssign: el tamaño de itemsAssign de cualquier solución siempre es igual al numero de items que tenemos de entrada
  - AllStrictlyPartial: todas las soluciones del modelo son estrictamente parciales (no completas).
  - HandleChildInvariantProperties: invariantes del método HandleChild.
  - LoopInvariant: invariantes del bucle.


  Lemas sobre soluciones parciales:
  - AllPartialProperties: añadir un hijo a una cola de soluciones parciales hace que la cola siga siendo de soluciones parciales.

  Lemas sobre la estructura de los árboles de búsqueda:
  - ParentNotInChildPartialExtensions: el padre no pertenece a las extensiones de sus hijos.
  - ChildrenAreDisjoint: las extensiones parciales del hijo true y del hijo false de una solución son disjuntas.

  Lemas sobre la preservación de DisjointTrees:
  - DisjointTreesPropertiesOneChild: si el padre era disjunto del resto de la cola (y los de la cola entre sí) entonces al quitar el padre y añadir un hijo se sigue cumpliendo esa propiedad.
  - DisjointTreesPropertiesTwoChildren: si añadimos los dos hijos a la cola se sigue cumpliendo la propiedad DisjointTrees.
  - SubsetDisjointTrees: si un conjunto s cumple la propiedad de DisjointTrees y s' esta contenido en s, entonces s' también cumple la propiedad de DisjointTrees.

  Lemas que demuestran la terminación:
  - StaticPartialPendingDecreases: al eliminar una solución del modelo de la cola, el conjunto de soluciones parciales pendientes decrece.
  - StaticPartialPendingWithSonDecreases: al eliminar una solución parcial de la cola y añadir uno de sus hijos, el conjunto de soluciones parciales pendientes decrece.
  - StaticPartialPendingWithSonsDecreases: al eliminar una solución parcial de la cola y añadir sus dos hijos, el conjunto de soluciones parciales pendientes decrece.

  Lemas para la corrección de prioridades:
  - PartialIncludePriority: las prioridades de las soluciones parciales pendientes son cotas superiores de las soluciones que pueden derivarse de ellas


  Métodos:
  - ComputeSolution: verificado. Encuentra una solución óptima que resuelve el problema mediante al método algorítmico de ramificación y poda.
  - Mainloop: verificado. implementa el bucle principal del algoritmo de ramificación y poda.
  - LoopBody: pendiente de verificar. Implementa una iteración del bucle principal del algoritmo de ramificación y poda.
  - HandleChild: verificado. inserta el hijo en la cola si este no es solución completa.
  - Main: verificado. Ejecuta el programa principal y muestra la solución.


---------------------------------------------------------------------------------------------------------------------*/

include "Item.dfy"
include "Input.dfy"
include "KnapsackPQ.dfy"
include "PQ.dfy"
include "../Specification/SolutionData.dfy"
include "../Specification/InputData.dfy"

import opened KnapsackPQ
import opened Input
import opened SolutionData
import opened Item
import opened InputData


/* Predicados*/

/* Predicado: el tamaño de itemsAssign de cualquier solución siempre es igual al numero de items que tenemos de entrada.*/
ghost predicate SameSizeItemsAssign(input : Input, m : multiset<Solution>)
  reads input, input.items, input.items[..]
  requires input.Valid()
  reads set i | i in m
  reads set i | i in m :: i.itemsAssign
{
  forall s | s in m :: s.itemsAssign.Length == input.items.Length
}


/* Predicado: todas las soluciones del modelo son estrictamente parciales (no completas).*/
ghost predicate AllStrictlyPartial(m : multiset<Solution>)
  reads m
{
  forall s <- m :: s.k < s.itemsAssign.Length
}


/* Predicado: invariantes del método HandleChild.*/
ghost predicate HandleChildInvariantProperties(pq : PriorityQueue, bs : Solution, input : Input)
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
  && SameSizeItemsAssign(input, pq.Model() + multiset{bs})
  && DistinctItemsAssign(pq.Model() + multiset{bs})
  && AllStrictlyPartial(pq.Model())
}


/* Predicado: invariantes del bucle. */
ghost predicate LoopInvariant(pq : PriorityQueue, bs : Solution, input : Input)
  reads pq, pq.arr, pq.arr[..]
  reads input, input.items, input.items[..]
  reads bs, bs.itemsAssign
  reads set i | 0 <= i < pq.arr.Length :: pq.arr[i].itemsAssign
{
  && HandleChildInvariantProperties(pq,bs,input)
  && BestSolutionIsUpperBound(input, bs, pq)
}



/* Lemas sobre soluciones parciales */

/*
Lema: añadir un hijo true o false a una cola de soluciones parciales hace que la cola siga siendo de soluciones parciales.
//
Propósito: Este lema se puede usar tanto cuando pretendemos añadir el hijo true como cuando después de añadir el true pretendemos añadir el false, ya que solo requiere que la cola sea de parciales
//
Verificación: trivial.
*/
lemma AllPartialProperties(parent : Solution, child : Solution, pq : PriorityQueue, input : Input)
  requires input.Valid()
  requires parent.Partial(input) && parent.Model().AllFalsesFromK()
  requires child.Partial(input) && child.Model().AllFalsesFromK()
  requires (child.IsFalseChild(parent, input) || child.IsTrueChild(parent, input))
  requires pq.Valid()
  requires child !in pq.Model()
  requires AllPartial(input, pq.Model())
  ensures AllPartial(input, pq.Model() + multiset{child})
{}


/* Lemas sobre la estructura de los árboles de búsqueda */

/*
Lema: el padre no pertenece a las extensiones de sus hijos.
//
Propósito: demostrar el lema StaticPartialPendingWithSonsDecreases.
//
Demostración: por reducción al absurdo.
*/
lemma ParentNotInChildPartialExtensions(input: Input, parent: Solution, child : Solution)
  requires input.Valid()
  requires parent.Partial(input) && parent.Model().AllFalsesFromK()
  requires child.Partial(input) && child.Model().AllFalsesFromK()
  requires child.IsTrueChild(parent, input) || child.IsFalseChild(parent,input)
  ensures parent.Model() !in child.Model().PartialExtensions()
{
  if parent.Model() in child.Model().PartialExtensions() {
    SolutionData.InPartialExtensions(input.Model(), child.Model(), parent.Model());
    assert false;
  }
}

/*
Lema: las extensiones parciales del hijo true y del hijo false de una solución son disjuntas.
//
Propósito: demostrar la disminución de StaticPartialPending cuando se añaden los dos hijos.
//
Demostración: por reducción al absurdo.
*/
lemma ChildrenAreDisjoint(parent : Solution, trueChild : Solution, falseChild: Solution, input : Input)
  requires input.Valid()
  requires parent.Partial(input) && parent.Model().AllFalsesFromK()
  requires trueChild.Partial(input) && trueChild.Model().AllFalsesFromK()
  requires trueChild.IsTrueChild(parent, input)
  requires falseChild.Partial(input) && falseChild.Model().AllFalsesFromK()
  requires trueChild.IsTrueChild(parent, input)
  requires falseChild.IsFalseChild(parent, input)
  ensures trueChild.Model().PartialExtensions() !! falseChild.Model().PartialExtensions()
{
  if !(trueChild.Model().PartialExtensions() !! falseChild.Model().PartialExtensions()) {
    assert trueChild.Model().PartialExtensions() * falseChild.Model().PartialExtensions() != {};
    ghost var s:| s in trueChild.Model().PartialExtensions() && s in falseChild.Model().PartialExtensions();

    assert parent.k == trueChild.k - 1 < |trueChild.Model().itemsAssign|;
    assert trueChild.Model() == SolutionData(parent.Model().itemsAssign[parent.k := true], parent.Model().k + 1);
    assert falseChild.Model() == SolutionData(parent.Model().itemsAssign[parent.k := false], parent.Model().k + 1);
    SolutionData.ItemsAssignSize(input.Model(),parent.Model(),s);
    SolutionData.InPartialExtensions(input.Model(),parent.Model(),s);
    assert |s.itemsAssign| == |parent.Model().itemsAssign|;
    SolutionData.ItemsAssignkth(input.Model(),parent.Model(),s,true);
    SolutionData.ItemsAssignkth(input.Model(),parent.Model(),s,false);
    assert s.itemsAssign[parent.k]==true;
    assert s.itemsAssign[parent.k]==false;
    assert false;
  }
}


/* Lemas de preservación de DisjointTrees */

/*
Lema: si el padre era disjunto del resto de la cola (y los de la cola entre sí) entonces al quitar el padre y añadir un hijo se sigue cumpliendo esa propiedad.
//
Propósito: demostrar la terminación de RyP cuando se añade a la cola solo uno de los dos hijos. 
//
Verificación: usando los lemas AllPartialProperties, SubsetDisjointTrees y ExtendsInPartialExtensions.
*/
lemma DisjointTreesPropertiesOneChild(parent : Solution, child : Solution, pq : PriorityQueue, input : Input)
  requires input.Valid()
  requires parent.Partial(input) && parent.Model().AllFalsesFromK()
  requires child.Partial(input) && child.Model().AllFalsesFromK()
  requires child.IsTrueChild(parent, input) || child.IsFalseChild(parent, input)
  requires pq.Valid()
  requires child !in pq.Model()
  requires AllPartial(input,pq.Model() + multiset{parent})
  requires DisjointTrees(input,pq.Model() + multiset{parent})
  ensures DisjointTrees(input,pq.Model() + multiset{child})
{
  AllPartialProperties(parent,child,pq,input);

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
Lema: si añadimos los dos hijos a la cola se sigue cumpliendo la propiedad DisjointTrees. 
//
Propósito: usarlo en la rama false si en la rama true se añadió el hijo true.
//
Verificación: usando los lemas AllPartialProperties, SubsetDisjointTrees, ItemsAssignSize, InPartialExtensions y ItemsAssignkth.
*/
lemma DisjointTreesPropertiesTwoChildren(parent : Solution, trueChild : Solution, falseChild: Solution, pq : PriorityQueue, input : Input)
  requires input.Valid()
  requires parent.Partial(input) && parent.Model().AllFalsesFromK()
  requires trueChild.Partial(input) && trueChild.Model().AllFalsesFromK()
  requires trueChild.IsTrueChild(parent, input)
  requires falseChild.Partial(input) && falseChild.Model().AllFalsesFromK()
  requires trueChild.IsTrueChild(parent, input)
  requires falseChild.IsFalseChild(parent, input)

  requires pq.Valid()
  requires trueChild !in pq.Model()
  requires falseChild !in pq.Model()
  requires AllPartial(input, pq.Model() + multiset{parent})
  requires DisjointTrees(input, pq.Model() + multiset{parent})

  ensures DisjointTrees(input, pq.Model() + multiset{trueChild} + multiset{falseChild})
{
  AllPartialProperties(parent, trueChild, pq, input);

  forall s | s in pq.Model() + multiset{trueChild} + multiset{falseChild}
    ensures (pq.Model() + multiset{trueChild} + multiset{falseChild})[s] == 1
  {
    if (s == parent) {}
    else if (s == trueChild) {}
    else if (s == falseChild) {}
    else {
      SubsetDisjointTrees(input, pq.Model() + multiset{parent}, pq.Model());
    }
  }

  ChildrenAreDisjoint(parent,trueChild,falseChild,input);

  forall z | z in pq.Model()
    ensures trueChild.Model().PartialExtensions() !! z.Model().PartialExtensions()
            && falseChild.Model().PartialExtensions() !! z.Model().PartialExtensions()
  {
    SolutionData.ExtendsInPartialExtensions(input.Model(), trueChild.Model(), parent.Model());
    SolutionData.ExtendsInPartialExtensions(input.Model(), falseChild.Model(), parent.Model());

    assert trueChild.Model() in parent.Model().PartialExtensions();
    assert falseChild.Model() in parent.Model().PartialExtensions();

    assert forall s | s in pq.Model() :: parent.Model().PartialExtensions() !! s.Model().PartialExtensions();
  }
}

/*
Lema: si un conjunto s cumple la propiedad de DisjointTrees y s' esta contenido en s, entonces s' también cumple la propiedad
de DisjointTrees.
//
Propósito: demsotrar el lema DisjointTreesPropertiesOneChild.
//
Verificación: trivial.
*/
lemma SubsetDisjointTrees(input : Input, s : multiset<Solution>, s' : multiset<Solution>)
  requires input.Valid()
  requires AllPartial(input, s)
  requires DisjointTrees(input, s)
  requires s' <= s
  ensures AllPartial(input, s')
  ensures DisjointTrees(input, s')
{}


/* Lemas que demuestran la terminación */

/*
Lema: al eliminar una solución s (el mínimo) de modelo de la cola, el conjunto de soluciones parciales 
pendientes decrece. 
//
Propósito: para demostrar la terminación del algoritmo RyP cuando se saca el mínimo de la cola.
//
Demostración: StaticPartialPending decrece porque s pertenece al modelo original de la cola (m). Al eliminar s,
el nuevo modelo deja de incluirla, lo cual hace que sea estrictamente menor. Esto se verifica con la ayuda de la propiedad de 
disjunción que nos dice que ninguno de los hijos de s contiene a s.
*/
lemma StaticPartialPendingDecreases(m: multiset<Solution>, parent: Solution, input : Input)
  requires parent in m
  requires input.Valid()
  requires AllPartial(input,m)
  requires DisjointTrees(input,m)
  ensures PriorityQueue.StaticPartialPending(m - multiset{parent}, input)
        < PriorityQueue.StaticPartialPending(m, input)
{
  assert PriorityQueue.StaticPartialPending(m - multiset{parent}, input) == PriorityQueue.StaticPartialPending(m, input) - parent.Model().PartialExtensions();
}


/*
Lema: al eliminar una solución parcial s de la cola y añadir sus dos hijos (trueChild y falseChild),
el conjunto de soluciones parciales pendientes decrece.
//
Propósito: demostrar la terminación en RyP cuando los dos hijos se añaden a la cola tras eliminar el padre.
//
Demostración: usando los lemas ExtendsInPartialExtensions y ParentNotInChildPartialExtensions.
*/
lemma StaticPartialPendingWithSonsDecreases(m: multiset<Solution>, parent: Solution, trueChild: Solution, falseChild: Solution, input : Input)
  requires input.Valid()
  requires parent in m
  requires 0 <= parent.k < |parent.Model().itemsAssign|
  requires parent.Partial(input)
  requires trueChild.Partial(input)
  requires falseChild.Partial(input)
  requires trueChild.Model().AllFalsesFromK()
  requires falseChild.Model().AllFalsesFromK()
  requires parent.Model().AllFalsesFromK()

  requires trueChild.IsTrueChild(parent,input)
  requires falseChild.IsFalseChild(parent,input)

  requires AllPartial(input,m)
  requires DisjointTrees(input,m)
  ensures PriorityQueue.StaticPartialPending((m - multiset{parent}) + multiset{trueChild, falseChild}, input)
        < PriorityQueue.StaticPartialPending(m, input)
{
  assert PriorityQueue.StaticPartialPending(m - multiset{parent}, input) == PriorityQueue.StaticPartialPending(m, input) - parent.Model().PartialExtensions();
  assert parent.Model() in PriorityQueue.StaticPartialPending(m, input);

  SolutionData.ExtendsInPartialExtensions(input.Model(),trueChild.Model(),parent.Model());
  SolutionData.ExtendsInPartialExtensions(input.Model(),falseChild.Model(),parent.Model());

  assert  trueChild.Model() in parent.Model().PartialExtensions();
  assert  falseChild.Model() in parent.Model().PartialExtensions();

  ParentNotInChildPartialExtensions(input, parent, trueChild);
  ParentNotInChildPartialExtensions(input, parent, falseChild);
}


/*
Lema: al eliminar una solución parcial s de la cola y añadir únicamente uno
de sus hijos, el conjunto de soluciones parciales pendientes decrece.
//
Propósito: demostrar la terminación del bucle de RyP cuando los dos hijos se añaden a la cola.
//
Demostración: usando los lemas StaticPartialPending, ExtendsInPartialExtensions y ParentNotInChildPartialExtensions.
*/
lemma StaticPartialPendingWithSonDecreases(m: multiset<Solution>, parent: Solution, child: Solution, input : Input)
  requires input.Valid()
  requires parent in m
  requires 0 <= parent.k < |parent.Model().itemsAssign|
  requires parent.Partial(input)
  requires child.Partial(input)
  requires child.IsFalseChild(parent,input) || child.IsTrueChild(parent,input)

  requires AllPartial(input,m)
  requires child.Model().AllFalsesFromK()
  requires parent.Model().AllFalsesFromK()
  requires DisjointTrees(input,m)
  ensures PriorityQueue.StaticPartialPending((m - multiset{parent}) + multiset{child}, input)
        < PriorityQueue.StaticPartialPending(m, input)
{
  assert PriorityQueue.StaticPartialPending(m - multiset{parent}, input) <= PriorityQueue.StaticPartialPending(m, input);
  assert parent.Model() in PriorityQueue.StaticPartialPending(m, input);

  SolutionData.ExtendsInPartialExtensions(input.Model(),child.Model(),parent.Model());
  assert  child.Model() in parent.Model().PartialExtensions();

  ParentNotInChildPartialExtensions(input, parent, child);
  assert parent.Model() !in child.Model().PartialExtensions();
  assert child.Model().PartialExtensions() < parent.Model().PartialExtensions();
}


/* Lemas para la corrección de las prioridades */

/*
Lema: AllPrioritiesAreCorrect se deduce de AllPartial para demostrar que las prioridades de las soluciones parciales pendientes 
son cotas superiores de las soluciones que pueden derivarse de ellas.
//
Propósito: verificar el método MainLoop.
// 
Demostración: usando el lema InExtensionsExtends.
*/
lemma PartialIncludePriority(pq : PriorityQueue, input : Input)
  requires input.Valid()
  requires pq.Valid() && AllPartial(input, pq.Model())
  ensures AllPrioritiesAreCorrect(input, pq.Model())
{
  forall p, s | p in pq.Model() &&  s in p.Model().Extensions() && s.Valid(input.Model())
    ensures s.TotalValue(input.Model().items) <= p.priority
  {
    assert s.Partial(input.Model());
    assert p.Model().IsUpperBound(p.priority,input.Model());
    SolutionData.InExtensionsExtends(input.Model(),p.Model(),s);
    assert s.Extends(p.Model());
  }
}



/* Métodos */

/*
Método: dado una entrada, encuentra la solución óptima mediante el bucle MainLoop. Para ello, 
se construyen dos soluciones:
 - Una solución parcial (ps): va generando la solución actual (decide las asignaciones de los objetos).
 - Una mejor solución (bs): almacena la mejor solución encontrada hasta el momento.
Ambas soluciones se inicializan con el array de asignaciones a falsos.
//
Verificación: se asegura que la mejor solución encontrada (bs) es tanto válida como óptima gracias 
a las postcondiciones del método MainLoop.
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
    assert LoopInvariant(pq, bs, input) by {
      assert bs.Valid(input) by {
        bs.Model().SumOfFalsesEqualsZero(input.Model());
      }
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
          {}
          assert sd.Extends(ps.Model());
          SolutionData.ExtendsInExtensions(input.Model(), sd, ps.Model());
          assert sd in ps.Model().Extensions();
        }
      }
    }
  }
}


/*
Método: implementa el bucle principal del algoritmo de ramificación y poda. Mientras que la cola de prioridad no esté vacía y su Min() 
sea superior al valor de la mejor solución encontrada, se continúa explorando el espacio de búsqueda mediante llamadas a LoopBody. 
El bucle utiliza como terminación el número de soluciones parciales pendientes, pq.PartialPending(input), que debe disminuir 
estrictamente en cada iteración.
//
Verificación: usando las postcondiciones de LoopBody y el lema PartialIncludePriority.
*/
method MainLoop(input: Input, pq: PriorityQueue, bs: Solution)
  modifies pq, pq.arr, bs, bs`totalValue, bs`totalWeight, bs`k, bs`itemsAssign, bs`priority, bs.itemsAssign
  requires LoopInvariant(pq, bs, input)
  ensures bs.Valid(input)
  ensures bs.Optimal(input)
{
  while !pq.IsEmpty() && pq.Min().priority > bs.totalValue
    decreases pq.PartialPending(input)
    invariant LoopInvariant(pq, bs, input)
    invariant pq.arr == old(pq.arr) || fresh(pq.arr)
    invariant bs.itemsAssign == old(bs.itemsAssign) || fresh(bs.itemsAssign)
  {
    LoopBody(bs, pq, input);
  }
  PartialIncludePriority(pq,input);
}


/*
Método: representa una iteración del bucle principal del algoritmo de ramificación y poda. Parte de
una cola no vacía, extrae de ella la solución parcial con mayor prioridad y genera sus dos hijos.
//
Verificación: pendiente de verificar.
*/
method {:axiom} LoopBody(bs : Solution, pq : PriorityQueue, input : Input)
  modifies pq, pq.arr, bs, bs`totalValue, bs`totalWeight, bs`k, bs`itemsAssign, bs`priority, bs.itemsAssign
  requires LoopInvariant(pq, bs, input)
  requires !pq.IsEmpty()
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

  // TRUE CHILD
  if parent.totalWeight + input.items[parent.k].weight <= input.maxWeight {
    trueChild := parent.NewTrueChild(input);
    HandleChild(trueChild, bs, pq, input);
  }

  // FALSE CHILD
  falseChild := parent.NewFalseChild(input);
  HandleChild(falseChild, bs, pq, input);
}



/*
Método: inserta el hijo en la cola si este no es solución completa.
//
Verificación: utilizando el lema PartialIncludePriority y varios asertos.
*/
method HandleChild(child : Solution, bs : Solution, pq : PriorityQueue, input : Input)
  modifies pq, pq.arr, bs, bs.itemsAssign

  // Invariantes del bucle
  requires HandleChildInvariantProperties(pq,bs,input)

  // Precondiciones sobre la válidez de child
  requires child.itemsAssign.Length == input.items.Length == bs.itemsAssign.Length
  requires child.Partial(input)
  requires child.Model().AllFalsesFromK()

  // Precondiciones acerca de la relación entre los diferentes objetos
  requires child !in pq.Model() // el hijo no pertenece a la cola
  requires child != bs // el hijo no es el objeto bs
  requires bs.itemsAssign != child.itemsAssign
  requires (forall s1 <- pq.Model() :: s1.itemsAssign != child.itemsAssign) // el hijo, bs y las soluciones de la cola tienen arrays diferentes
  requires DisjointTrees(input, pq.Model() + multiset{child})


  // Invariantes del bucle
  ensures HandleChildInvariantProperties(pq, bs, input) 

  // Postcondiciones sobre la cola
  ensures pq.arr == old(pq.arr) || fresh(pq.arr)
  ensures if (child.k < child.itemsAssign.Length && child.priority > bs.totalValue)
          then pq.Model() == old(pq.Model()) + multiset{child}
          else pq.Model() == old(pq.Model())
  ensures bs.itemsAssign == old(bs.itemsAssign) || fresh(bs.itemsAssign)
{
  if (child.priority > bs.totalValue) {
    if (child.k == child.itemsAssign.Length) {
      bs.Copy(child);
      assert pq.Valid();
      assert if (child.k != child.itemsAssign.Length && child.priority > bs.totalValue)
            then pq.Model() == old(pq.Model()) + multiset{child}
            else pq.Model() == old(pq.Model());
      assert pq.arr == old(pq.arr) || fresh(pq.arr);
      assert child != bs;
      assert child.itemsAssign != bs.itemsAssign;
      assert (forall s : Solution | s in pq.Model() :: s.k < s.itemsAssign.Length);
    }
    else {
      assert child.priority > bs.totalValue && child.k < child.itemsAssign.Length;

      pq.Insert(child);

      assert DisjointTrees(input, pq.Model());
      assert DisjointTrees(input, old(pq.Model()) + multiset{child});
      assert DisjointTrees(input, pq.Model());

      assert HandleChildInvariantProperties(pq,bs,input) by {
        assert bs.Valid(input) && bs !in pq.Model();
        assert AllPartial(input, pq.Model());
        assert SameSizeItemsAssign(input, pq.Model() + multiset{bs});
        assert AllStrictlyPartial(pq.Model());
        assert DistinctItemsAssign(pq.Model() + multiset{bs});
        PartialIncludePriority(pq,input);
        assert AllPrioritiesAreCorrect(input, pq.Model());
      }
    }
  }
  else {}
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

  for i := 0 to bs.itemsAssign.Length {
    if (bs.itemsAssign[i]) {
      print "Item ", i," with weight: ", input.items[i].weight, " and value: ", input.items[i].value;
    }
  }
  print "\nTotal weight: ", bs.totalWeight, "\n";

}

