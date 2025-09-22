//include "Implementation/Solution.dfy"

module Q {
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
        var count : int  // current number of elements, if count == arr.Length, array must grow


        constructor PriorityQueue(size: int)
            //ensures this.IsHeap()
        {
            this.arr := new Solution[0];
            this.count := 0;
        }


        /* Predicates */

        /* Predicate: true if the array satisfies the heap property */
        predicate IsHeap() 
            reads this, this.arr, set i | 0 <= i < this.arr.Length :: arr[i]
        {
            && 0 <= this.count <= arr.Length
            && (forall i | 0 < i < this.count :: this.arr[(i-1)/2].priority < this.arr[i].priority)
        }

        /* Predicate: true if the heap has no elements */
        predicate IsEmpty()
            reads this
        {
            this.count == 0
        }



        /* Methods */

        /* Method: return the maximum capacity of the heap */
        method Size() returns (s : int)
        {
            return this.arr.Length;
        }


        /* Method: returns the current number of elements in the heap */
        method Count() returns (c : int)
        {
            return this.count;
        }


        /* Method: returns the element with the minimum priority in the heap */
        method Min() returns (m : Solution)
            requires 0 < this.count <= this.arr.Length <= this.arr.Length
            requires this.IsHeap()
        {
            return this.arr[0];
        }

        
        /* Method: inserts an element to the heap */
        method Insert(node : Solution)
            modifies this, this.arr
            requires this.IsHeap()
            requires 0 < this.arr.Length == this.arr.Length
            ensures this.IsHeap()
        {
            if (this.count == this.arr.Length) {
                Grow(node);
            }
            this.count := this.count + 1;
            this.Float();     
        }

        /* Method: duplicates space of the heap */
        method Grow(x : Solution)
            modifies this, this.arr
            requires 0 <= this.count == this.arr.Length
            ensures this.count == old(this.count) // el numero de elementos no aumenta, lo hace Insert
            ensures this.arr[0..this.count] == old(this.arr[0..this.count]) // los primeros elementos que habia antes en el array se conservan
            ensures this.arr.Length > old(this.arr.Length) // la longitud aumenta
            ensures fresh(this.arr) // es nuevo en la memoria
        {
            // allocate new memory
            var aux: array<Solution> := new Solution[2 * this.arr.Length + 1] (_ => x);
            
            assert this.count == this.arr.Length;
            // copy
            var i := 0;
            while i < this.count
                decreases this.count-i
                invariant 0 <= i <= this.count <= this.arr.Length < aux.Length && this.count == old(this.count)
                invariant aux[0..i] == this.arr[0..i]
                invariant this.arr[0..this.count] == old(this.arr[0..this.count])
            {
                aux[i] := this.arr[i];
                i := i + 1;
            }
            assert aux[0..this.count] == this.arr[0..this.count] == old(this.arr[0..this.count]);
            //assert Seq.Rev(aux[0..size]) == Seq.Rev(list[0..size]) == Seq.Rev(old(list[0..size]));
            this.arr := aux;
            //assert Model() == Seq.Rev(aux[0..size]);
        }


        /* Method: */
        method Float()
            modifies this.arr
            requires 0 < this.count <= this.arr.Length
            requires forall i | 0 < i < this.count - 1 :: this.arr[(i-1)/2].priority <= this.arr[i].priority
            ensures this.IsHeap()
        



        /* Method: returns the element with the minimum priority of the heap */
        method DeleteMin()
            modifies this, this.arr
            requires this.IsHeap()
            requires 0 < this.count
            //ensures this.IsHeap()
        {
            this.arr[0] := this.arr[this.count - 1];
            this.count := this.count - 1;
            //Sink(0, this.count);
        }


        /* Method: the element with the minimum priority of the heap */
        method Sink(s : nat, l : nat)
            modifies this.arr
            requires 0 <= s <= l == this.count <= arr.Length
            requires forall i | 0 < i < this.count && (i-1)/2 != s :: this.arr[(i-1)/2].priority <= this.arr[i].priority
            ensures this.IsHeap()
        


        
    }
}