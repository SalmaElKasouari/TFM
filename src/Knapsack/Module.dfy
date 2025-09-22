//include "Implementation/Solution.dfy"

abstract module Q {
    class Solution {
        var priority : real

        ghost predicate Compare(other : Solution)
            reads this, other
        {
           this.priority < other.priority 
        }
    }

    /*
     The following priority queue is implemented with a williams heap (binary heap)
    */
    class PriorityQueue {
        var arr : array<Solution>
        var size : int // fixed size of arr

        constructor PriorityQueue(arr': array<Solution>, size': int)
            ensures this.arr == arr'
            ensures this.size == size'
        {
            this.arr := arr';
            this.size := size';
        }

        //methods

        
    }
}