include "PQ.dfy"
include "Item.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"

module KnapsackPQ refines PQ {

  import opened Input
  import opened InputData
  import opened SolutionData

  class PriorityQueue ... {



    /* Functions */

    /* 
      Function: devuelve el conjunto de soluciones válidas (completas) de la cola que todavía no han sido procesadas. 
    */
    ghost function Pending(input : Input) : set<SolutionData>
      reads input, input.items, input.items[..]
      reads this, arr, arr[..]
      reads set i | 0 <= i < arr.Length :: arr[i].itemsAssign
      requires input.Valid()
      requires Valid()
    {
      set s : Solution, sd : SolutionData |
        && s in Model() && s.Partial(input) && sd.Valid(input.Model())
        && sd in s.Model().Extensions() ::sd
    }

    /* 
      Function: devuelve el conjunto de soluciones parciales de la cola que todavía no han sido procesadas. Sirve para la 
      terminación del bucle del algoritmo RyP.
    */
    ghost function PartialPending(input : Input) : set<SolutionData>
      reads input, input.items, input.items[..]
      reads this, arr,set i | 0 <= i < arr.Length :: arr[i]
      reads set i | 0 <= i < arr.Length :: arr[i].itemsAssign
      requires input.Valid()
      requires Valid()
    {
      StaticPartialPending(Model(),input)
    }


    /* 
      Function: devuelve el conjunto de soluciones parciales del modelo (m) que todavía no han sido procesadas.
    */
    static ghost function StaticPartialPending(m: multiset<Solution>, input : Input) : set<SolutionData>
      reads input, input.items, input.items[..]
      reads m, set s <- m :: s.itemsAssign
      requires input.Valid()
    {
      set s : Solution, sd : SolutionData |
        && s in m && s.Partial(input) && sd.Partial(input.Model())
        && sd in s.Model().PartialExtensions() :: sd
    }
  }


  /* Predicados */

  /* Predicado: el tamaño de itemsAssign de cualquier solución siempre es igual al numero de items que tenemos de entrada.*/
  ghost predicate SameSizeItemsAssign(input : Input, m : multiset<Solution>)
    reads input, input.items, input.items[..]
    requires input.Valid()
    reads set i | i in m
    reads set i | i in m :: i.itemsAssign
  {
    forall s | s in m :: s.itemsAssign.Length == input.items.Length
  }


  /* Predicado: todas las soluciones son parciales y tienen todas las pocisiones desde k a false.*/
  ghost predicate AllPartial(input : Input, m : multiset<Solution>)
    reads input, input.items, input.items[..]
    requires input.Valid()
    reads set i | i in m
    reads set i | i in m :: i.itemsAssign
  {
    forall s | s in m :: s.Partial(input) && s.Model().AllFalsesFromK()
  }


  /* Predicado: las extensiones de un nodo del modelo no pertenecen a otras extensiones de otro nodo del modelo.*/
  ghost predicate DisjointTrees(input : Input, m : multiset<Solution>)
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


  /* Predicado: todas las soluciones del modelo tienen itemsAssign diferentes.*/
  ghost predicate DistinctItemsAssign(m : multiset<Solution>)
    reads m
  {
    forall s1 <- m, s2 <- m | s1 != s2 :: s1.itemsAssign != s2.itemsAssign
  }


  /* Predicado: todas las soluciones del modelo son estrictamente parciales (no completas).*/
  ghost predicate AllStrictlyPartial(m : multiset<Solution>)
    reads m
  {
    forall s <- m :: s.k < s.itemsAssign.Length
  }


  /* Predicado: la prioridad de cada solución parcial es una cota superior del valor total de cualquier extensión válida de dicha solución. */
  ghost predicate AllPrioritiesAreCorrect(input : Input, m : multiset<Solution>)
    reads m
    reads set i | i in m
    reads set i | i in m :: i.itemsAssign
    reads input, input.items, input.items[..]
    requires input.Valid()
    requires forall i : Solution | i in m :: i.k <= i.itemsAssign.Length
  {
    forall p <- m, s <- p.Model().Extensions() | s.Valid(input.Model())
      :: s.TotalValue(input.Model().items) <= p.priority
  }


  /* Predicado: toda solución válida que ya no está pendiente tiene un valor total menor o igual que la mejor solución */
  ghost predicate BestSolutionIsUpperBound(input : Input, bs : Solution, pq : PriorityQueue)
    reads input, input.items, input.items[..]
    reads pq, pq.arr, pq.arr[..]
    reads set i | 0 <= i < pq.arr.Length :: pq.arr[i].itemsAssign
    reads bs
    requires input.Valid()
    requires pq.Valid()
  {
    forall sd : SolutionData
      | sd.Valid(input.Model()) && sd !in pq.Pending(input)
      :: sd.TotalValue(input.Model().items) <= bs.totalValue
  }


  /* Lemas */

  /*
  Lema: garantiza que al eliminar una solución s (el mínimo) de modelo de la cola, el conjunto de soluciones parciales 
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
    assert parent.Model() in PriorityQueue.StaticPartialPending(m, input);
  }


  /*
  Lema: garantiza que al eliminar una solución parcial s de la cola y añadir sus dos hijos (trueChild y falseChild),
  el conjunto de soluciones parciales pendientes decrece.
  //
  Propósito: demostrar la terminación en RyP cuando los dos hijos se añadena  a la cola.
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

    // assert parent.Model() !in trueChild.Model().PartialExtensions();
    // assert parent.Model() !in falseChild.Model().PartialExtensions();

    // assert trueChild.Model().PartialExtensions() < parent.Model().PartialExtensions();
    // assert falseChild.Model().PartialExtensions() < parent.Model().PartialExtensions();

    // ChildrenAreDisjoint(parent,trueChild,falseChild,input);
    // assert trueChild.Model().PartialExtensions() !! falseChild.Model().PartialExtensions();

    // assert PriorityQueue.StaticPartialPending((m - multiset{parent}) + multiset{trueChild, falseChild}, input)
    //     == PriorityQueue.StaticPartialPending(m - multiset{parent}, input) +
    //        (set sd:SolutionData | sd.Partial(input.Model()) && sd in trueChild.Model().PartialExtensions()) +
    //        (set sd:SolutionData | sd.Partial(input.Model()) && sd in falseChild.Model().PartialExtensions());
    // assert PriorityQueue.StaticPartialPending((m - multiset{parent}) + multiset{trueChild, falseChild}, input)  <= PriorityQueue.StaticPartialPending(m, input);
    // assert parent.Model() !in PriorityQueue.StaticPartialPending(m - multiset{parent}, input);
    // assert parent.Model() !in PriorityQueue.StaticPartialPending((m - multiset{parent}) + multiset{trueChild, falseChild}, input);
  }


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

  //------
  lemma ParentNotInChildExtensions(parent : Solution, child : Solution, input : Input)
    requires input.Valid()
    requires parent.Partial(input) && parent.Model().AllFalsesFromK()
    requires child.Partial(input) && child.Model().AllFalsesFromK()
    requires child.IsTrueChild(parent, input) || child.IsFalseChild(parent,input)
    ensures parent.Model() !in child.Model().PartialExtensions()
  {
    assert parent.k == child.k - 1 < |child.Model().itemsAssign|;
    if parent.Model() in child.Model().PartialExtensions()
    {
      SolutionData.InPartialExtensions(input.Model(),child.Model(),parent.Model());
      assert parent.k > child.k;
      assert false;
    }
  }

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
    if !(trueChild.Model().PartialExtensions() !! falseChild.Model().PartialExtensions())
    {
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
  //---------------


  /*
  Lema: garantiza que al eliminar una solución parcial s de la cola y añadir únicamente uno
  de sus hijos, el conjunto de soluciones parciales pendientes decrece.
  //
  Propósito: 
  //
  Demostración: 
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

    // assume PriorityQueue.StaticPartialPending((m - multiset{parent}) + multiset{child}, input)
    //     == PriorityQueue.StaticPartialPending(m - multiset{parent}, input) +
    //        child.Model().PartialExtensions();
    // assert PriorityQueue.StaticPartialPending((m - multiset{parent}) + multiset{child}, input)  <= PriorityQueue.StaticPartialPending(m, input);
    // assert parent.Model() !in PriorityQueue.StaticPartialPending(m - multiset{parent}, input);
    // assert parent.Model() !in PriorityQueue.StaticPartialPending((m - multiset{parent}) + multiset{child}, input);

  }


  /*
  Lema: si un conjunto s cumple la propiedad de DisjointTrees y s' esta contenido en s, 
  entonces s' también cumple la propiedad de DisjointTrees.
  //
  Propósito: demsotrar el lema DisjointTreesPropertiesOneChild.
  //
  Verificación: trivial
  */
  lemma SubsetDisjointTrees(input : Input, s : multiset<Solution>, s' : multiset<Solution>)
    requires input.Valid()
    requires AllPartial(input, s)
    requires DisjointTrees(input, s)
    requires s' <= s
    ensures AllPartial(input, s')
    ensures DisjointTrees(input, s')
  {}


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


  /*
  Lema: si el padre era disjunto del resto de la cola (y los de la cola entre sí) entonces al quitar el padre y añadir el hijo true sigue cumpliendo esa propiedad.
  //
  Propósito: solo se puede usar cuando se añade a la cola uno de los dos hijos, es decir, en la rama true y en la rama false solo si no se ha añadido el true antes. 
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
  Propósito: Este hay que usarle en la rama false si en la rama true se añadió
  el hijo true.
  //
  Verificación:
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

    assert trueChild.Model().PartialExtensions() !! falseChild.Model().PartialExtensions() by {
      if !(trueChild.Model().PartialExtensions() !! falseChild.Model().PartialExtensions()) {
        assert trueChild.Model().PartialExtensions() * falseChild.Model().PartialExtensions() != {};
        ghost var s:| s in trueChild.Model().PartialExtensions() && s in falseChild.Model().PartialExtensions();

        assert parent.k == trueChild.k - 1 < |trueChild.Model().itemsAssign|;
        assert trueChild.Model() == SolutionData(parent.Model().itemsAssign[parent.k := true], parent.Model().k + 1);
        assert falseChild.Model() == SolutionData(parent.Model().itemsAssign[parent.k := false], parent.Model().k + 1);
        SolutionData.ItemsAssignSize(input.Model(), parent.Model(), s);
        SolutionData.InPartialExtensions(input.Model(), parent.Model(), s);
        assert |s.itemsAssign| == |parent.Model().itemsAssign|;

        SolutionData.ItemsAssignkth(input.Model(), parent.Model(), s, true);
        assert s.itemsAssign[parent.k] == true;

        SolutionData.ItemsAssignkth(input.Model(), parent.Model(), s, false);
        assert s.itemsAssign[parent.k] == false;

        assert false;
      }
    }

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



  class Solution ... {

    /* Atributos y constructor */

    var itemsAssign: array<bool>
    var totalValue: real
    var totalWeight: real
    var k: nat
    var priority : real

    constructor(itemsAssign': array<bool>, totalV: real, totalW: real, k': nat, prio : real)
      ensures itemsAssign == itemsAssign'
      ensures totalValue == totalV
      ensures totalWeight == totalW
      ensures k == k'
      ensures priority == prio
    {
      itemsAssign := itemsAssign';
      totalValue := totalV;
      totalWeight := totalW;
      k := k';
      priority := prio;
    }


    /* Predicados */


    /* 
    Predicado: define el orden estricto (<) entre dos soluciones. Devuelve true si this tiene una 
    prioridad estrictamente menor que other.
    */
    predicate lt (other : Solution)
      ensures !other.lt(other)
    {
      priority > other.priority
    }


    /* Lema: demuestra que lt is irreflexivo */
    static lemma LtIrreflexive(){}

    /* Lema: demuestra que lt is asimetrico */
    static lemma LtAntisymmetric(){}

    /* Lema: demuestra que lt is transitivo */
    static lemma LtTransitive(){}

    /* Lema: demuestra que le is transitivo */
    static lemma LeTransitive() {}

    /* Lema: demuestra que lt cumple la incomparabilidad transitiva */
    static lemma LtTransitiveIncomparability(){}



    /* 
    Predicado: verifica que una solución parcial sea válida, es decir, que su modelo sea válido y que el peso y el valor de los 
    objetos seleccionados coincidan con los valores del modelo.
    */
    ghost predicate Partial (input : Input)
      reads this, itemsAssign, input, input.items, input.items[..]
      requires input.Valid()
    {
      && 0 <= k <= itemsAssign.Length
      && IsUpperBound(input)
      && Model().Partial(input.Model())
      && Model().TotalWeight(input.Model().items) == totalWeight
      && Model().TotalValue(input.Model().items) == totalValue
    }


    /* 
    Predicado: verifica si la solución representa una cota superior válida para el problema definido por el input dado.
    */
    ghost predicate IsUpperBound(input : Input)
      reads this, itemsAssign, input, input.items, input.items[..]
      requires input.Valid()
    {
      Model().IsUpperBound(priority, input.Model())
    }


    /* 
    Predicado: verifica si la solución es válida y completa (todos los objetos han sido tratados (k == itemsAssign.Length).
    */
    ghost predicate Valid (input : Input)
      reads this, itemsAssign, input, input.items, input.items[..]
      requires input.Valid()

    {
      && k == itemsAssign.Length
      && Partial(input)
    }


    /* 
    Predicado: garantiza que una solución válida sea óptima en relación con el modelo del problema.
    */
    ghost predicate Optimal(input: Input)
      reads this, itemsAssign, input, input.items, input.items[..]
      requires input.Valid()
      requires Valid(input)
    {
      Model().Optimal(input.Model())
    }


    /* 
    Predicado: verifica que this es el nodo hijo extendido con true de parent.
    */
    ghost predicate IsTrueChild(parent: Solution, input : Input)
      reads this, itemsAssign, parent, parent.itemsAssign, input,  input.items, input.items[..]
    {
      && k <= itemsAssign.Length == parent.itemsAssign.Length == input.items.Length
      && k == parent.k + 1 // el hijo tiene una posición más
      && Model().Extends(parent.Model()) // el hijo extiende al padre: son iguales hasta parent.k
      && itemsAssign[k-1] == true // en esa posición adicional, el hijo tiene true
    }


    /* 
    Predicado: verifica que this es el nodo hijo extendido con false de parent.
    */
    ghost predicate IsFalseChild(parent: Solution, input : Input)
      reads this, itemsAssign, parent, parent.itemsAssign, input,  input.items, input.items[..]
    {
      && k <= itemsAssign.Length == parent.itemsAssign.Length == input.items.Length
      && k == parent.k + 1 // el hijo tiene una posición más
      && Model().Extends(parent.Model()) // el hijo extiende al padre: son iguales hasta parent.k
      && itemsAssign[k-1] == false // en esa posición adicional, el hijo tiene false
    }



    /* Functions */

    /*
    Function: devuelve un SolutionData, el modelo de una solución.
    */
    ghost function Model() : SolutionData
      reads this, itemsAssign
    {
      SolutionData(itemsAssign[..], k)
    }


    /*
    Function: calcula el número de etapas restantes en la solución parcial. Es la Function de bound del Method algorítmico
    de vuelta atrás.
    */
    ghost function Bound() : int
      reads this
    {
      itemsAssign.Length - k + 1
    }


    /*
    Function: devuelve la prioridad del nodo.
    */
    function Priority() : real
      reads this
    {
      priority
    }



    /* Methods */

    /*
    Method: copia los valores de una solución s a otra solución this, garantizando que todos los atributos de 
    la solución copiada this sea completamente idética a s, manteniendo la consistencia del modelo.
    //
    Verificación: se usa un invariante en el bucle que establece que en
    cada iteración i del bucle, todos los elementos anteriores a i en el array itemsAssign son iguales a los 
    correspondientes elementos de s.itemsAssign.
    */
    method Copy(s : Solution)
      modifies this`totalValue, this`totalWeight, this`k, itemsAssign, this`priority
      requires this != s
      requires itemsAssign.Length == s.itemsAssign.Length
      ensures k == s.k
      ensures totalValue == s.totalValue
      ensures totalWeight == s.totalWeight
      ensures priority == s.priority
      ensures itemsAssign == old(itemsAssign)
      ensures forall i | 0 <= i < itemsAssign.Length :: itemsAssign[i] == s.itemsAssign[i]
      ensures Model() == s.Model()
    {
      // Copiar los elementos del array uno por uno
      for i := 0 to s.itemsAssign.Length
        invariant 0 <= i <= s.itemsAssign.Length
        invariant forall j | 0 <= j < i :: itemsAssign[j] == s.itemsAssign[j]
      {
        itemsAssign[i] := s.itemsAssign[i];
      }
      totalValue := s.totalValue;
      totalWeight := s.totalWeight;
      k := s.k;
      priority := s.priority;
    }


    /* Método: constructor de copia. Crea un nuevo objeto solución que es copia de s. */
    constructor CloneCopy(s : Solution)
      ensures itemsAssign.Length == s.itemsAssign.Length
      ensures k == s.k
      ensures totalValue == s.totalValue
      ensures totalWeight == s.totalWeight
      ensures priority == s.priority
      ensures forall i | 0 <= i < itemsAssign.Length :: itemsAssign[i] == s.itemsAssign[i]
      ensures Model() == s.Model()
      ensures fresh(itemsAssign)
    {
      totalValue := s.totalValue;
      totalWeight := s.totalWeight;
      k := s.k;
      priority := s.priority;

      // Copiar los elementos del array uno por uno
      new;
      itemsAssign := new bool[s.itemsAssign.Length];
      assert itemsAssign.Length == s.itemsAssign.Length;
      for i := 0 to s.itemsAssign.Length
        modifies itemsAssign
        invariant 0 <= i <= s.itemsAssign.Length == itemsAssign.Length
        invariant forall j | 0 <= j < i :: itemsAssign[j] == s.itemsAssign[j]
      {
        itemsAssign[i] := s.itemsAssign[i];
      }
    }


    /*
    Método: devuelve el hijo que extiende al padre con true.
    //
    Verificación: trivial.
    */
    method NewTrueChild(input : Input) returns (trueChild : Solution)
      requires k < itemsAssign.Length == input.items.Length
      requires input.Valid()
      requires Partial(input)
      requires totalWeight + input.items[k].weight <= input.maxWeight // es factible
      requires Model().AllFalsesFromK()
      ensures trueChild.IsTrueChild(this, input)
      ensures trueChild.Partial(input)
      ensures fresh(trueChild)
      ensures trueChild.Model().AllFalsesFromK()
      ensures fresh(trueChild.itemsAssign)
    {
      trueChild := new Solution.CloneCopy(this);
      trueChild.itemsAssign[trueChild.k] := true;
      trueChild.totalWeight := totalWeight + input.items[trueChild.k].weight;
      trueChild.totalValue := totalValue + input.items[trueChild.k].value;
      trueChild.priority := priority;
      trueChild.k := trueChild.k + 1;

      Solution.PartialConsistency(trueChild, this, input);
    }


    /*
    Método: devuelve el hijo que extiende al padre con false.
    //
    Verificación: con el lema AddFalsePreservesWeightValue.
    */
    method NewFalseChild(input : Input) returns (falseChild : Solution)
      requires k < itemsAssign.Length == input.items.Length
      requires input.Valid()
      requires Partial(input)
      requires Model().AllFalsesFromK()
      ensures falseChild.IsFalseChild(this, input)
      ensures falseChild.Partial(input)
      ensures fresh(falseChild)
      ensures fresh(falseChild.itemsAssign)
      ensures falseChild.Model().AllFalsesFromK()
    {
      falseChild := new Solution.CloneCopy(this);
      falseChild.itemsAssign[falseChild.k] := false;
      falseChild.totalWeight := totalWeight;
      falseChild.totalValue := totalValue;
      falseChild.k := falseChild.k + 1;

      SolutionData.AddFalsePreservesWeightValue(Model(), falseChild.Model(), input.Model()); // necesaria para poder llamar a CalculateUpperBound que exige: SolutionData(itemsAssign[..], k).TotalValue(input.Model().items) == totalValue, propiedad que garantiza Partial()
      falseChild.CalculateUpperBound(input);
    }


    /*
    Método: cálculo la cota superior de la mejor solución alcanzable. La cota superior consiste en seleccionar todos los objetos restantes.
    //
    Verificación: usando el lema AllTruesIsUpperBoundForAll.
    */
    method CalculateUpperBound(input : Input)
      modifies `priority
      requires input.Valid()
      requires 0 <= k <= input.items.Length == itemsAssign.Length
      requires Model().Partial(input.Model())
      requires Model().TotalWeight(input.Model().items) == totalWeight
      requires Model().TotalValue(input.Model().items) == totalValue
      ensures Partial(input)
      /*
      requires 0 <= k <= itemsAssign.Length
      requires 0 <= k <= input.items.Length == itemsAssign.Length
      requires SolutionData(itemsAssign[..], k).TotalValue(input.Model().items) == totalValue
      ensures
        forall s : SolutionData
          | && |s.itemsAssign| == |SolutionData(itemsAssign[..], k).itemsAssign|
            && s.k == |s.itemsAssign|
            && k <= s.k
            && s.Extends(SolutionData(itemsAssign[..], k))
            && s.Valid(input.Model())
          :: s.TotalValue(input.Model().items) <= upperBound
          */
    {
      ghost var ps' := SolutionData(itemsAssign[..], k);
      assert |ps'.itemsAssign| == |itemsAssign[..]|;
      priority := totalValue;

      assert priority == ps'.TotalValue(input.Model().items);

      for i := k to itemsAssign.Length
        invariant k <= ps'.k <= |ps'.itemsAssign| == |itemsAssign[..]|
        invariant ps'.Extends(SolutionData(itemsAssign[..], k))
        invariant forall j | k <= j < i :: ps'.itemsAssign[j]
        invariant i == ps'.k
        invariant priority == ps'.TotalValue(input.Model().items)
      {
        var oldps' := ps';
        ps' := SolutionData(ps'.itemsAssign[ps'.k := true], ps'.k+1);
        priority := priority + input.items[i].value;
        SolutionData.AddTrueMaintainsSumConsistency(oldps', ps', input.Model());
      }
      SolutionData.AllTruesIsUpperBoundForAll(SolutionData(itemsAssign[..], k), ps', input.Model());
    }



    /* Lemas */

    /* 
    Lema: dada una solución s que es válida por un input dado, y this tiene el mismo modelo, peso acumulado 
    y valor acumulado que s, entonces this también será válida para el mismo input. 
    //
    Propósito: demostrar que el TotalValue de ps es igual al TotalValue de bs en KnapsackBTBaseCase de BT.dfy.
    //
    Demostración: trivial.
    */
    lemma CopyModel (s : Solution, input : Input)
      requires input.Valid()
      requires s.Valid(input)
      requires s.Model() == Model()
      requires s.totalWeight == totalWeight
      requires s.totalValue == totalValue
      requires s.priority == priority
      ensures Valid(input)
    {}


    /*
    Lema: si extendemos una solución parcial (parent) añadiendo un elemento asignado como (true) 
    dando lugar a una nueva solución parcial (trueChild), entonces ps también cumple con las propiedades de consistencia 
    parcial definidas por el método Partial. 
    //
    Propósito: garantizar que ps sigue siendo Partial en KnapsackBTTrueBranch después de añadirle un objeto cuyo peso 
    no hacía exceder el peso maximo.
    //
    Verificación: se realizan cálculos formales para demostrar que el valor y peso de ps son consistentes con oldps:
      - Primer calc: Se usa el lema AddTrueMaintainsSumConsistency para garantizar que el peso total de ps es la suma 
        del peso de parent mas el nuevo Item. Se usa el lema InputDataItems para garantizar que el peso total de ps es la suma 
        del peso de parent mas el nuevo ItemData. Finalmente se garantiza que el peso total es menor que el peso máximo.
      - Segundo calc: se parte de ps.totalWeight y se reescribe como la suma de oldtotalWeight y el nuevo Item. Se 
        asegura que oldtotalWeight es igual a parent.TotalWeight(input.Model().items). Y se usan los lemas InputDataItems 
        y AddTrueMaintainsSumConsistency para demostrar que la transición de parent a ps es válida. Se asegura que la 
        suma se puede reescribir como ps.Model().TotalWeight(input.Model().items).
      - Tercer calc: análogo al anterior pero aplicado al valor total en lugar del peso.
    */
    static lemma PartialConsistency(ps: Solution, parent: Solution, input: Input)
      requires input.Valid()
      requires 1 <= ps.k <= ps.itemsAssign.Length
      requires 0 <= parent.k <= parent.itemsAssign.Length
      requires ps.k == parent.k + 1
      requires ps.itemsAssign.Length == parent.itemsAssign.Length == input.items.Length
      requires parent.itemsAssign[..parent.k] + [true] == ps.itemsAssign[..ps.k]
      requires parent.Partial(input)
      requires parent.totalWeight + input.items[ps.k - 1].weight <= input.maxWeight
      requires parent.totalWeight == ps.totalWeight - input.items[parent.k].weight
      requires parent.totalValue == ps.totalValue - input.items[parent.k].value
      requires ps.IsTrueChild(parent, input)
      requires ps.priority == parent.priority
      ensures ps.Partial(input)
    {
      calc {
         ps.totalWeight;
        { SolutionData.AddTrueMaintainsSumConsistency(parent.Model(), ps.Model(), input.Model()); }
         parent.totalWeight + input.Model().items[ps.k - 1].weight;
        { input.InputDataItems(ps.k - 1); }
         parent.totalWeight + input.items[ps.k - 1].weight;
      <= input.maxWeight;
      }

      calc {
        ps.totalWeight;
        parent.totalWeight + input.items[ps.k - 1].weight;
        parent.Model().TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
        { input.InputDataItems(ps.k - 1);
          SolutionData.AddTrueMaintainsSumConsistency(parent.Model(), ps.Model(), input.Model());
        }
        ps.Model().TotalWeight(input.Model().items);
      }

      calc {
        ps.totalValue;
        parent.totalValue + input.items[ps.k - 1].value;
        parent.Model().TotalValue(input.Model().items) + input.items[ps.k - 1].value;
        { input.InputDataItems(ps.k - 1);
          SolutionData.AddTrueMaintainsSumConsistency(parent.Model(), ps.Model(), input.Model());
        }
        ps.Model().TotalValue(input.Model().items);
      }

      Solution.EqualPriorityImpliesPartial(parent, ps, input);
      assert ps.Model().IsUpperBound(ps.priority, input.Model());
      assert ps.Partial(input);
    }


    /*
    Lema: si una solución parent es Partial (su prioridad es cota superior) y su hijo trueChild extendido con true tiene la misma 
    prioridad que su padre, entonces la prioridad del hijo es cota superior.
    //
    Propósito: demostrar que ps es Partial en el lema PartialConsistency
    //
    Verificación: trivial.
    */
    static lemma EqualPriorityImpliesPartial(parent : Solution, trueChild : Solution, input : Input)
      requires input.Valid()
      requires parent.Partial(input)
      requires trueChild.IsTrueChild(parent, input)
      requires trueChild.priority == parent.priority
      ensures trueChild.IsUpperBound(input)
    {}


  }

}