include "PQ.dfy"
include "Item.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"

module KnapsackPQ refines PQ {

  import opened Input
  import opened InputData
  //import opened SolutionData

  ghost function rootData(input : InputData) : SolutionData
  {
    SolutionData(seq(|input.items|, i => false), 0)
  }

  //Una SolutionData que extiende a otra que no es parcial no puede ser solucion valida
  lemma ExtendsNotPartialNotValid(input : InputData, s : SolutionData, f : SolutionData)
    decreases |input.items| - f.k
    requires input.Valid()
    requires !f.Partial(input)
    requires f.k <= s.k == |s.itemsAssign| == |f.itemsAssign| == |input.items|
    requires s.Extends(f)
    ensures !s.Valid(input)
  {
    if (f.k == s.k) {
      assert s.itemsAssign[..] == f.itemsAssign[..];
      assert s == f;
    }
    else {
      var ftrue := SolutionData(f.itemsAssign[f.k := true], f.k + 1);
      var ffalse := SolutionData(f.itemsAssign[f.k := false], f.k + 1);
      assert s.Extends(ftrue) || s.Extends(ffalse);
      assert !f.Implicit(input.items, input.maxWeight);

      if (s.Extends(ftrue)) {
        SolutionData.AddTrueMaintainsSumConsistency(f, ftrue, input);
        assert !ftrue.Partial(input);
        ExtendsNotPartialNotValid(input, s, ftrue);
      } else {
        SolutionData.AddFalsePreservesWeightValue(f, ffalse, input);
        assert !ffalse.Partial(input);
        ExtendsNotPartialNotValid(input, s, ffalse);
      }
    }
  }


  //Una SolutionData valida que extiende a otra parcial ha de estar en el conjunto Extensions de dicha solucion parcial
  lemma ExtendsInExtensions(input : InputData, s : SolutionData, f : SolutionData)
    decreases |input.items| - f.k
    requires input.Valid()
    requires s.Valid(input) && f.Partial(input)
    requires s.Extends(f)
    ensures s in f.Extensions()
  {
    if (s.k == f.k) {
      assert s.k == |input.items|;
      assert s.itemsAssign[..] == f.itemsAssign[..];
      assert s == f;
    }
    else {
      var ftrue := SolutionData(f.itemsAssign[f.k := true], f.k + 1);
      var ffalse := SolutionData(f.itemsAssign[f.k := false], f.k + 1);
      assert s.Extends(ftrue) || s.Extends(ffalse);
      if (s.Extends(ftrue)) {
        if (ftrue.Partial(input)) { }
        else { ExtendsNotPartialNotValid(input, s, ftrue);}
      }
      else {
        if (ffalse.Partial(input)) { }
        else { ExtendsNotPartialNotValid(input, s, ffalse);}
      }
    }
  }


  //Todas las SolutionData extienden a la raiz del arbol y por tanto estan en sus extensiones
  lemma AllSolutions(input : InputData, s : SolutionData)
    requires input.Valid()
    requires s.Valid(input)
    ensures s.Extends(rootData(input))
    ensures s in rootData(input).Extensions()
  {
    ExtendsInExtensions(input, s, rootData(input));
  }


  //
  lemma AllNodes(input: InputData, s: SolutionData)
    requires input.Valid()
    requires s.Partial(input)
    requires |s.itemsAssign| == |input.items|
    ensures s.Extends(rootData(input))
    ensures s in rootData(input).PartialExtensions()
  {
    ExtendsInPartialExtensions(input, s, rootData(input));
  }


  lemma SamePrefixSameNode(s : SolutionData, f : SolutionData)
    decreases |s.itemsAssign| - s.k
    requires 0 <= s.k < |s.itemsAssign| == |f.itemsAssign|
    requires 0 <= f.k < |f.itemsAssign|
    requires s.itemsAssign[0..s.k] == f.itemsAssign[0..s.k]
    ensures s == f
  // {
  //   if (s.k == |s.itemsAssign|) {
  //     //assert s == f;
  //   }
  //   else {
  //     ghost var s' := SolutionData(s.itemsAssign, s.k + 1);
  //     ghost var f' := SolutionData(f.itemsAssign[f.k := s'.itemsAssign[s'.k]], f.k + 1);
  //     assert s'.itemsAssign[0..s'.k] == f'.itemsAssign[0..f'.k];
  //     SamePrefixSameNode(s', f);
  //   }
  // }


  lemma ExtendsInPartialExtensions(input : InputData, s : SolutionData, f : SolutionData)
    //decreases |input.items| - f.k
    requires input.Valid()
    requires f.k <= s.k
    requires s.Partial(input) && f.Partial(input)
    requires s.Extends(f)
    ensures s in f.PartialExtensions()
  {
    if (s.k == f.k) {
      if (s.k == |input.items|) {
        assert s == f;
      }
      else {
        assert s.itemsAssign[0..s.k] == f.itemsAssign[0..f.k];
        assert forall i | 0 <= i < f.k :: f.itemsAssign[i] == f.itemsAssign[i];
        assert f in f.PartialExtensions(); //demo de forall del extends ==> la linea anterior
        assume false;
        //SamePrefixSameNode(s, f);
      }
    }
    else {
      assume s == f;
    }
  }



  class PriorityQueue ... {

    ghost function Pending(input : Input) : set<SolutionData>
      reads input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      reads this, this.arr,set i | 0 <= i < this.arr.Length :: this.arr[i]
      reads set i | 0 <= i < this.arr.Length :: this.arr[i].itemsAssign
      requires input.Valid()
      requires Valid()
    { set s : Solution, sd : SolutionData |
        && s in Model() && s.Partial(input) && sd.Valid(input.Model())
        && sd in s.Model().Extensions() ::sd
    }


    ghost function PartialPending(input : Input) : set<SolutionData>
      reads input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      reads this, this.arr,set i | 0 <= i < this.arr.Length :: this.arr[i]
      reads set i | 0 <= i < this.arr.Length :: this.arr[i].itemsAssign
      requires input.Valid()
      requires this.Valid()
    {
      set s : Solution, sd : SolutionData |
        && s in this.Model() && s.Partial(input) && sd.Partial(input.Model())
        && sd in s.Model().PartialExtensions() :: sd
    }

    ghost predicate AllPartial(input:Input)
      reads input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      reads this, this.arr,set i | 0 <= i < this.arr.Length :: this.arr[i]
      reads set i | 0 <= i < this.arr.Length :: this.arr[i].itemsAssign
      requires input.Valid()
      requires Valid()
    {
      forall s | s in Model() ::s.Partial(input)
    }

    static ghost function RecPartialPending(input:Input, model:multiset<Solution>):set<SolutionData>
      reads input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      reads model, set s:Solution | s in model ::s.itemsAssign
      requires input.Valid()
    {
      if (model == multiset{}) then {}
      else
        var s:| s in model;
        if (s.Partial(input)) then s.Model().PartialExtensions() + RecPartialPending(input,model-multiset{s})
        else RecPartialPending(input,model-multiset{s})
    }

    ghost predicate disJointTrees(input:Input)
      reads input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      reads this, this.arr,set i | 0 <= i < this.arr.Length :: this.arr[i]
      reads set i | 0 <= i < this.arr.Length :: this.arr[i].itemsAssign
      requires input.Valid()
      requires Valid()
      requires AllPartial(input)
    { 
      forall s1, s2 | s1 in Model() && s2 in Model() && s1 != s2 :: s1.Model() !in s2.Model().PartialExtensions()
    }

    static ghost function RecMPartialPending(input:Input, model:multiset<Solution>):multiset<SolutionData>
      reads input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      reads model, set s:Solution | s in model ::s.itemsAssign
      requires input.Valid()
    {
      if (model == multiset{}) then multiset{}
      else
        var s:| s in model;
        if (s.Partial(input)) then multiset(s.Model().PartialExtensions()) + RecMPartialPending(input,model-multiset{s})
        else RecMPartialPending(input,model-multiset{s})
    }

    lemma nonEmpty(input:Input)
      requires input.Valid()
      requires this.Valid()
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
      ensures this.itemsAssign == itemsAssign'
      ensures this.totalValue == totalV
      ensures this.totalWeight == totalW
      ensures this.k == k'
      ensures this.priority == prio
    {
      this.itemsAssign := itemsAssign';
      this.totalValue := totalV;
      this.totalWeight := totalW;
      this.k := k';
      this.priority := prio;
    }


    /* Predicates */


    /* 
    Predicate: define el orden estricto (<) entre dos soluciones. Devuelve true si this tiene una 
    prioridad estrictamente menor que other.
    */
    predicate lt (other : Solution)
      ensures !other.lt(other)
    {
      this.priority > other.priority
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
      reads this, this.itemsAssign, input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      requires input.Valid()
    {
      && 0 <= this.k <= this.itemsAssign.Length
      && IsUpperBound(input)
      && Model().Partial(input.Model())
      && Model().TotalWeight(input.Model().items) == totalWeight
      && Model().TotalValue(input.Model().items) == totalValue
    }


    /* 
    Predicate: verifica si la solución representa una cota superior válida para el problema definido por el input dado.
    */
    ghost predicate IsUpperBound(input : Input)
      reads this, this.itemsAssign, input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      requires input.Valid()
    {
      Model().IsUpperBound(this.priority, input.Model())
    }


    /* 
    Predicate: verifica si la solución es válida y completa (todos los objetos han sido tratados (k == itemsAssign.Length).
    */
    ghost predicate Valid (input : Input)
      reads this, this.itemsAssign, input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      requires input.Valid()

    {
      && this.k == this.itemsAssign.Length
      && Partial(input)
    }


    /* 
    Predicate: garantiza que una solución válida sea óptima en relación con el modelo del problema.
    */
    ghost predicate Optimal(input: Input)
      reads this, this.itemsAssign, input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      requires input.Valid()
      requires this.Valid(input)
    {
      this.Model().Optimal(input.Model())
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
      this.itemsAssign.Length - this.k + 1
    }


    /*
    Function: devuelve la prioridad del nodo.
    */
    function Priority() : real
      reads this
    {
      this.priority
    }



    /* Methods */

    /*
    Method: copia los valores de una solución s a otra solución this, garantizando que todos los atributos de 
    la solución copiada this sea completamente idética a s, manteniendo la consistencia del modelo.
    //
    Verificación: se usa un invariante en el bucle que establece que en
    cada iteración i del bucle, todos los elementos anteriores a i en el array this.itemsAssign son iguales a los 
    correspondientes elementos de s.itemsAssign.
    */
    method Copy(s : Solution)
      modifies this`totalValue, this`totalWeight, this`k, this.itemsAssign, this`priority
      requires this != s
      requires this.itemsAssign.Length == s.itemsAssign.Length
      ensures this.k == s.k
      ensures this.totalValue == s.totalValue
      ensures this.totalWeight == s.totalWeight
      ensures this.priority == s.priority
      ensures this.itemsAssign == old(this.itemsAssign)
      ensures forall i | 0 <= i < this.itemsAssign.Length :: this.itemsAssign[i] == s.itemsAssign[i]
      ensures this.Model() == s.Model()
    {

      // Copiar los elementos del array uno por uno
      for i := 0 to s.itemsAssign.Length
        invariant 0 <= i <= s.itemsAssign.Length
        invariant forall j | 0 <= j < i :: this.itemsAssign[j] == s.itemsAssign[j]
      {
        this.itemsAssign[i] := s.itemsAssign[i];
      }
      this.totalValue := s.totalValue;
      this.totalWeight := s.totalWeight;
      this.k := s.k;
      this.priority := s.priority;
    }

    constructor CCopy(s : Solution)
      ensures this.itemsAssign.Length == s.itemsAssign.Length
      ensures this.k == s.k
      ensures this.totalValue == s.totalValue
      ensures this.totalWeight == s.totalWeight
      ensures this.priority == s.priority
      ensures forall i | 0 <= i < this.itemsAssign.Length :: this.itemsAssign[i] == s.itemsAssign[i]
      ensures this.Model() == s.Model()
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
      requires s.Model() == this.Model()
      requires s.totalWeight == this.totalWeight
      requires s.totalValue == this.totalValue
      requires s.priority == this.priority
      ensures this.Valid(input)
    {}

  }

}