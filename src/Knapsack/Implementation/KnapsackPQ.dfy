include "PQ.dfy"

module KnapsackPQ refines PQ {
  class Payload {
    var s : Solution

    constructor (s: Solution)
      ensures this.s == s
    {
      this.s := s;
    }
  }

  // Aquí no implementamos Compare, sigue abstracto.
  // La idea es que el usuario lo tenga que implementar en su Solution.
}