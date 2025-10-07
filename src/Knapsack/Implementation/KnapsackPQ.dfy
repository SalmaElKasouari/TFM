include "PQ.dfy"
include "Item.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"

module KnapsackPQ refines PQ {

  import opened Input
  import opened SolutionData

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
    Predicate: defines the non-strict ordering (<=) between two solutions. Returns true if this solution 
    has a priority less than or equal to the other. This predicate is defined in 
    terms of 'lt', so that this.le(other) <==> Not(other.lt(this)).
    */
    predicate le (other : Solution)
    {
      !other.lt(this)
    }


    /* 
    Predicate: defines the strict ordering (<) between two solutions. Returns true if this solution 
    has a strictly lower priority than the other.
    */
    predicate lt (other : Solution)
      ensures !other.lt(other)
    {
      this.priority < other.priority
    }

    /* 
    Predicate: no element is related to itself, not(x < x) 
    */
    predicate Irreflexive (x : Solution)
      reads x
    {
      !x.lt(x)
    }

    /* 
    Predicate: if a < b, then not b < a 
    */
    predicate Asymmetric (x : Solution, y : Solution)
      reads x, y
    {
      x.lt(y) ==> !y.lt(x)
    }

    /* 
    Predicate: if a < b and b < c, then a < c
    */
    predicate Transitive (x : Solution, y : Solution, z : Solution)
      reads x, y, z
    {
      x.lt(y) && y.lt(z) ==> x.lt(z)
    }

    /* 
    Predicate: weak ordering — if neither a < b nor b < a, they are equivalent
    */
    predicate WeakOrder(x : Solution, y : Solution)
      reads x, y
    {
      (!x.lt(y) && !y.lt(x)) ==> x.priority == y.priority
    }

    /* Lemma: proof that lt is irreflexive */
    lemma LtIrreflexive()
      ensures forall x : Solution :: Irreflexive(x)
    {}

    /* Lemma: proof that lt is asymmetric */
    lemma LtAsymmetric()
      ensures forall x, y : Solution :: Asymmetric(x, y)
    {}

    /* Lemma: proof that lt is transitive */
    lemma LtTransitive()
      ensures forall x, y, z : Solution :: Transitive(x, y, z)
    {}

    /* Lemma: proof that lt satisfies weak order */
    lemma LtWeakOrder()
      ensures forall x, y : Solution :: WeakOrder(x, y)
    {}


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
    Predicate: checks whether the solution represents a valid upper bound for the problem model defined 
    by the given input.
    */
    ghost predicate IsUpperBound(input : Input)
      reads this, this.itemsAssign, input, input.items, set i | 0 <= i < input.items.Length :: input.items[i]
      requires input.Valid()
      //requires this.Valid(input)
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
    ghost function Priority() : real
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
        invariant forall j | 0 <= j < i :: this.itemsAssign[j] == s.itemsAssign[j]
      {
        this.itemsAssign[i] := s.itemsAssign[i];
      }
      this.totalValue := s.totalValue;
      this.totalWeight := s.totalWeight;
      this.k := s.k;
      this.priority := s.priority;
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