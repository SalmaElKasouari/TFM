include "../Knapsack/Implementation/PQ.dfy"

module ValuePQ refines PQ {

  class PriorityQueue ... {}

  class Solution ... {

    var value : real

    constructor(value': real)
      ensures value == value'
    {
      value := value';
    }

    
    function GetValue() : real
    reads this, this`value
    {
      value
    }

    /* 
    Predicado: define el orden estricto (<) entre dos soluciones.
    */
    predicate lt (other : Solution)
      ensures !other.lt(other)
    {
      value < other.value
    }
  }

}

