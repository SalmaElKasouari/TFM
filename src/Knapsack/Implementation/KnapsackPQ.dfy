include "PQ.dfy"
include "Item.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"

module KnapsackPQ refines PQ {

  import opened Input
  import opened InputData
  import opened SolutionData

  class PriorityQueue ... {

    /* Predicates */

    /* 
      Predicate: verifica que todas las soluciones de la cola sean parciales.
    */
    ghost predicate AllPartial(input:Input)
      reads input, input.items, input.items[..]
      reads this, arr,set i | 0 <= i < arr.Length :: arr[i]
      reads set i | 0 <= i < arr.Length :: arr[i].itemsAssign
      requires input.Valid()
      requires Valid()
    {
      forall s | s in Model() :: s.Partial(input) && s.Model().AllFalsesFromK()
    }

    /* 
      Predicate: verifica que el modelo de la cola sea un conjunto, esto es, que todas las soluciones de la cola aparecen 
      exactamente una vez en el modelo. Además verifica que todo par de soluciones del modelo de la cola son disjuntas, es decir,
      que ninfuna solución se encuentra en las extensiones parciales de otra.
    */
    ghost predicate DisjointTrees(input : Input)
      reads input, input.items, input.items[..]
      reads this, arr,set i | 0 <= i < arr.Length :: arr[i]
      reads set i | 0 <= i < arr.Length :: arr[i].itemsAssign
      requires input.Valid()
      requires Valid()
      requires AllPartial(input)
    {
      && (forall s | s in Model() :: Model()[s] == 1)
      && (forall s1, s2 | s1 in Model() && s2 in Model() && s1 != s2 :: s1.Model() !in s2.Model().PartialExtensions())
    }



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
      set s : Solution, sd : SolutionData |
        && s in Model() && s.Partial(input) && sd.Partial(input.Model())
        && sd in s.Model().PartialExtensions() :: sd
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


    /*
      Lemma: garantiza que al eliminar una solución s (el mínimo) de modelo de la cola, el conjunto de soluciones parciales 
      pendientes decrece. 
      //
      Propósito: para demostrar la terminación del algoritmo RyP cuando se saca el mínimo de la cola.
      //
      Demostración: StaticPartialPending decrece porque s pertenece al modelo original de la cola (m). Al eliminar s,
      el nuevo modelo deja de incluirla, lo cual hace que sea estrictamente menor. Esto se verifica con la ayuda de la propiedad de 
      disjunción que nos dice que ninguno de los hijos de s contiene a s.
    */
    static lemma StaticPartialPendingDecreases(m: multiset<Solution>, s: Solution, input : Input)
      requires s in m
      requires input.Valid()
      requires forall s <- m :: s.Partial(input) // && s.Model().Partial(input.Model()) && s.Model().k <= |s.Model().itemsAssign|
      requires assert (forall s <- m :: s.Partial(input) && s.Model().Partial(input.Model()) && s.Model().k <= |s.Model().itemsAssign|); true
      requires (forall s | s in m :: m[s] == 1)
      requires (forall s1 <- m, s2 <- m | s1 != s2 :: s1.Model() !in s2.Model().PartialExtensions())
      ensures StaticPartialPending(m - multiset{s}, input)
            < StaticPartialPending(m, input)
    {
      assert StaticPartialPending(m - multiset{s}, input) <= StaticPartialPending(m, input);
      assert s.Model() in StaticPartialPending(m, input);
      // forall S
      //   | S in m - multiset{s} && S.Partial(input) && s.Model().Partial(input.Model())
      //   ensures s.Model() !in S.Model().PartialExtensions()
      // {
      //   assert s != S;
      // }
      //assert s.Model() !in StaticPartialPending(m - multiset{s}, input);
    }

    /*
      Lemma: garantiza que al eliminar una solución s (el mínimo) de modelo de la cola, el conjunto de soluciones parciales 
      pendientes decrece. 
      //
      Propósito: para demostrar la terminación del algoritmo RyP cuando se saca el mínimo de la cola y se añaden sus hijos.
      //
      Demostración: 
    */
    static lemma StaticPartialPendingWithSonsDecreases(m: multiset<Solution>, s: Solution, leftSon: Solution, rightSon: Solution, input : Input)
      requires s in m
      requires 0 <= s.k <= |s.Model().itemsAssign|
      requires leftSon.Model() in s.Model().PartialExtensions() // leftSon es hijo de s
      requires rightSon.Model() in s.Model().PartialExtensions() // rightSon es hijo de s
      requires input.Valid()
      requires forall s <- m :: s.Partial(input)
      requires leftSon.Partial(input)
      requires rightSon.Partial(input)

      requires assert (forall s <- m :: s.Partial(input) && s.Model().Partial(input.Model()) && s.Model().k <= |s.Model().itemsAssign|); true
      requires (forall s | s in m :: m[s] == 1)
      requires (forall s1 <- m, s2 <- m | s1 != s2 :: s1.Model() !in s2.Model().PartialExtensions())

      ensures StaticPartialPending((m - multiset{s}) + multiset{leftSon, rightSon}, input)
            < StaticPartialPending(m, input)
    {
      assert StaticPartialPending(m - multiset{s}, input) <= StaticPartialPending(m, input);
      assert s.Model() in StaticPartialPending(m, input);
      PriorityQueue.StaticPartialPendingDecreases(m, s, input);

      assume false;
    }

    /*
      Lemma: garantiza que al eliminar una solución s (el mínimo) de modelo de la cola, el conjunto de soluciones parciales 
      pendientes decrece. 
      //
      Propósito: para demostrar la terminación del algoritmo RyP cuando se saca el mínimo de la cola y se añaden sus hijos.
      //
      Demostración: 
    */
    // static lemma StaticPartialPendingWithSonsDecreases2(m: multiset<Solution>, s: Solution, input : Input)
    //   requires s in m
    //   requires 0 <= s.k <= |s.Model().itemsAssign|
    //   requires input.Valid()
    //   requires forall s <- m :: s.Partial(input)
    //   requires assert (forall s <- m :: s.Partial(input) && s.Model().Partial(input.Model()) && s.Model().k <= |s.Model().itemsAssign|); true
    //   requires (forall s | s in m :: m[s] == 1)
    //   requires (forall s1 <- m, s2 <- m | s1 != s2 :: s1.Model() !in s2.Model().PartialExtensions())

    //   ensures StaticPartialPending(m - multiset{s} + multiset(s.Model().PartialExtensions()), input)
    //         < StaticPartialPending(m, input)
    // {
    //   assert StaticPartialPending(m - multiset{s}, input) <= StaticPartialPending(m, input);
    //   assert s.Model() in StaticPartialPending(m, input);
    //   PriorityQueue.StaticPartialPendingDecreases(m, s, input);
    //   assert leftSon.Model() !in StaticPartialPending(m, input);
    //   assert rightSon.Model() !in StaticPartialPending(m, input);

    //   assert StaticPartialPending(m - multiset{s} + multiset{leftSon} + multiset{rightSon}, input) <= StaticPartialPending(m, input);
    //   assert s.Model() in StaticPartialPending(m, input);
    //   forall S
    //     | S in m - multiset{s} && S.Partial(input) && s.Model().Partial(input.Model())
    //     ensures s.Model() !in S.Model().PartialExtensions()
    //   {
    //     assert s != S;
    //   }
    //   assert s.Model() !in StaticPartialPending(m - multiset{s}, input);
    // }







    lemma MinInPartialPending(input: Input)
      requires input.Valid()
      requires Valid()
      requires !IsEmpty()
      requires AllPartial(input)
      ensures Min().Model() in PartialPending(input)
    {}

    //--------------------------------------

    static ghost function RecPartialPending(input:Input, model:multiset<Solution>):set<SolutionData>
      reads input, input.items, input.items[..]
      reads model, set s:Solution | s in model ::s.itemsAssign
      requires input.Valid()
    {
      if (model == multiset{}) then {}
      else
        var s:| s in model;
        if (s.Partial(input)) then s.Model().PartialExtensions() + RecPartialPending(input,model-multiset{s})
        else RecPartialPending(input,model-multiset{s})
    }

    static ghost function RecMPartialPending(input:Input, model:multiset<Solution>):multiset<SolutionData>
      reads input, input.items, input.items[..]
      reads model, set s:Solution | s in model ::s.itemsAssign
      requires input.Valid()
    {
      if (model == multiset{}) then multiset{}
      else
        var s:| s in model;
        if (s.Partial(input)) then multiset(s.Model().PartialExtensions()) + RecMPartialPending(input,model-multiset{s})
        else RecMPartialPending(input,model-multiset{s})
    }

    lemma NonEmpty(input:Input)
      requires input.Valid()
      requires Valid()
      requires forall s:Solution | s in Model() :: s.Partial(input)
      requires !IsEmpty()
      ensures PartialPending(input) != {}
      ensures RecPartialPending(input,Model()) != {}
      ensures RecMPartialPending(input,Model()) != multiset{}
    {
      var s:Solution :| s in Model() && s.Partial(input);
      var sd := s.Model();
      assert sd in s.Model().PartialExtensions();
      assert sd in PartialPending(input);
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


    /* Predicates */


    /* 
    Predicate: define el orden estricto (<) entre dos soluciones. Devuelve true si this tiene una 
    prioridad estrictamente menor que other.
    */
    predicate lt (other : Solution)
      ensures !other.lt(other)
    {
      priority > other.priority
    }


    /* Lemma: demuestra que lt is irreflexivo */
    static lemma LtIrreflexive(){}

    /* Lemma: demuestra que lt is asimetrico */
    static lemma LtAntisymmetric(){}

    /* Lemma: demuestra que lt is transitivo */
    static lemma LtTransitive(){}

    /* Lemma: demuestra que le is transitivo */
    static lemma LeTransitive() {}

    /* Lemma: demuestra que lt cumple la incomparabilidad transitiva */
    static lemma LtTransitiveIncomparability(){}



    /* 
    Predicate: verifica que una solución parcial sea válida, es decir, que su modelo sea válido y que el peso y el valor de los 
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
    Predicate: verifica si la solución representa una cota superior válida para el problema definido por el input dado.
    */
    ghost predicate IsUpperBound(input : Input)
      reads this, itemsAssign, input, input.items, input.items[..]
      requires input.Valid()
    {
      Model().IsUpperBound(priority, input.Model())
    }


    /* 
    Predicate: verifica si la solución es válida y completa (todos los objetos han sido tratados (k == itemsAssign.Length).
    */
    ghost predicate Valid (input : Input)
      reads this, itemsAssign, input, input.items, input.items[..]
      requires input.Valid()

    {
      && k == itemsAssign.Length
      && Partial(input)
    }


    /* 
    Predicate: garantiza que una solución válida sea óptima en relación con el modelo del problema.
    */
    ghost predicate Optimal(input: Input)
      reads this, itemsAssign, input, input.items, input.items[..]
      requires input.Valid()
      requires Valid(input)
    {
      Model().Optimal(input.Model())
    }


    /* 
    Predicate: verifica que this es el nodo hijo extendido con true de parent.
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
    Predicate: verifica que this es el nodo hijo extendido con false de parent.
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
    static lemma PartialConsistency(ps: Solution, parent: Solution, input: Input, oldtotalWeight: real, oldtotalValue: real)
      requires input.Valid()
      requires 1 <= ps.k <= ps.itemsAssign.Length
      requires 0 <= parent.k <= parent.itemsAssign.Length
      requires ps.k == parent.k + 1
      requires ps.itemsAssign.Length == parent.itemsAssign.Length == input.items.Length
      requires parent.itemsAssign[..parent.k] + [true] == ps.itemsAssign[..ps.k]
      requires parent.Partial(input)
      requires oldtotalWeight == parent.Model().TotalWeight(input.Model().items)
      requires oldtotalValue == parent.Model().TotalValue(input.Model().items)
      requires parent.Model().TotalWeight(input.Model().items) + input.items[ps.k - 1].weight <= input.maxWeight
      requires oldtotalWeight == ps.totalWeight - input.items[parent.k].weight
      requires oldtotalValue == ps.totalValue - input.items[parent.k].value
      requires ps.IsTrueChild(parent, input)
      requires ps.priority == parent.priority
      ensures ps.Partial(input)
    {
      assert parent.Partial(input);
      assert oldtotalWeight == parent.Model().TotalWeight(input.Model().items);
      assert parent.Model().TotalWeight(input.Model().items) + input.items[ps.k - 1].weight <= input.maxWeight;

      calc {
         ps.Model().TotalWeight(input.Model().items);
        { SolutionData.AddTrueMaintainsSumConsistency(parent.Model(), ps.Model(), input.Model()); }
         parent.Model().TotalWeight(input.Model().items) + input.Model().items[ps.k - 1].weight;
        { input.InputDataItems(ps.k - 1); }
         parent.Model().TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
      <= input.maxWeight;
      }

      calc {
        ps.totalWeight;
        oldtotalWeight + input.items[ps.k - 1].weight;
        parent.Model().TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
        { input.InputDataItems(ps.k - 1);
          SolutionData.AddTrueMaintainsSumConsistency(parent.Model(), ps.Model(), input.Model());
        }
        ps.Model().TotalWeight(input.Model().items);
      }

      calc {
        ps.totalValue;
        oldtotalValue + input.items[ps.k - 1].value;
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

    static lemma EqualPriorityImpliesPartial(parent : Solution, trueChild : Solution, input : Input)
      requires input.Valid()
      requires parent.Partial(input)
      requires trueChild.IsTrueChild(parent, input)
      requires trueChild.priority == parent.priority
      ensures trueChild.IsUpperBound(input) // trueChild.Model().IsUpperBound(trueChild.priority, input.Model())
    {}

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
    {
      trueChild := new Solution.CloneCopy(this);
      trueChild.itemsAssign[trueChild.k] := true;
      trueChild.totalWeight := totalWeight + input.items[trueChild.k].weight;
      trueChild.totalValue := totalValue + input.items[trueChild.k].value;
      trueChild.priority := priority;
      trueChild.k := trueChild.k + 1;

      Solution.PartialConsistency(trueChild, this, input, this.totalWeight, this.totalValue);
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
      ensures falseChild.Model().AllFalsesFromK()
    {
      falseChild := new Solution.CloneCopy(this);
      falseChild.itemsAssign[falseChild.k] := false;
      falseChild.totalWeight := totalWeight;
      falseChild.totalValue := totalValue;
      falseChild.k := falseChild.k + 1;

      SolutionData.AddFalsePreservesWeightValue(Model(), falseChild.Model(), input.Model()); // necesaria para poder llamar a CalculateUpperBound que exige: SolutionData(itemsAssign[..], k).TotalValue(input.Model().items) == totalValue, propiedad que garantiza Partial()
      falseChild.priority := falseChild.CalculateUpperBound(falseChild.itemsAssign, falseChild.k, falseChild.totalValue, input);
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

  }

}