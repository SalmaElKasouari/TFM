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
    var count : int  // current number of elements, if count == arr.Length, array must grow


    constructor PriorityQueue(size: int)
      //ensures this.Valid()
    {
      this.arr := new Solution[0];
      this.count := 0;
    }


    /* Predicates */

    /* Predicate: true if the segment [x, y) of the array satisfies the heap property*/
    predicate isHeap(x : int, y : int)
      reads this, this.arr, set i | 0 <= i < this.arr.Length :: arr[i]
    {
      && 0 <= x <= y <= arr.Length
      && (forall i | x < i < y :: this.arr[(i-1)/2].priority < this.arr[i].priority)
    }

    /* Predicate: true if the array satisfies the heap property */
    predicate Valid()
      reads this, this.arr, set i | 0 <= i < this.arr.Length :: arr[i]
    {
      this.isHeap(0, this.count)
    }


    /* Predicate: true if the heap has no elements */
    predicate IsEmpty()
      reads this
    {
      this.count == 0
    }



    /* Methods */

    /* Method: returns the current number of elements in the heap */
    method Size() returns (c : int)
    {
      return this.count;
    }


    /* Method: returns the element with the minimum priority in the heap */
    method Min() returns (m : Solution)
      requires 0 < this.count <= this.arr.Length <= this.arr.Length
      requires this.Valid()
    {
      return this.arr[0];
    }


    /* Method: inserts an element to the heap */
    method Insert(node : Solution)
      modifies this, this.arr
      requires this.Valid()
      //ensures this.Valid()
    {

      if (this.IsEmpty()) {
        var aux: array<Solution> := new Solution[1][node];
        this.arr := aux;
      }
      else if (this.count < this.arr.Length) { // array is not full
        this.arr[this.count] := node;
      }
      else { // array is full
        Grow();
        this.arr[this.count] := node;
      }
      this.count := this.count + 1;
      this.Float();      
    }


    /* Method: duplicates space of the heap */
    method Grow()        
      modifies this, this.arr
      requires 0 < this.count == this.arr.Length
      ensures this.count == old(this.count) // the number of elements does not change in this method. The Method Insert increases it
      ensures this.arr.Length > old(this.arr.Length) // the length of the array increases
      ensures fresh(this.arr) // is new in memory
      ensures this.arr[0..this.count] == old(this.arr[0..this.count]) // the elements that were already in the array are preserved
    {
      // allocate new memory
      var last := this.arr[this.count-1];
      var aux: array<Solution> := new Solution[2 * this.arr.Length] (_ => last);

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


    /* Method: moves the last inserted node upward in the heap until the heap property is restored */
    method Float()
      modifies this.arr
      requires 0 < this.count <= this.arr.Length
      requires forall i | 0 < i < this.count - 1 :: this.arr[(i-1)/2].priority <= this.arr[i].priority
      ensures this.Valid()
    // {
    //     var j := this.count - 1;
    //     while j > 0 && this.arr[(j-1)/2].priority > this.arr[j].priority
    //         invariant 0 <= j <= this.count - 1 < this.arr.Length
    //         invariant forall i | 0 < i < this.count :: i != j ==> this.arr[(i-1)/2].priority <= this.arr[i].priority
    //     {
    //         this.arr[(j-1)/2], this.arr[j] := this.arr[j], this.arr[(j-1)/2];
    //         j := (j-1)/2;
    //     }
    // }



    /* Method: deletes the element with the minimum priority of the heap */
    method DeleteMin()
      modifies this, this.arr
      requires this.Valid()
      requires 0 < this.count
      //ensures this.Valid()
    {
      this.arr[0] := this.arr[this.count - 1];
      this.count := this.count - 1;
      //Sink(0, this.count);
    }


    /* Method: moves a node downward in the heap until the heap property is restored */
    method Sink(s : nat, l : nat)
      modifies this.arr
      requires 0 <= s <= l == this.count <= arr.Length
      requires forall i | 0 < i < this.count && (i-1)/2 != s :: this.arr[(i-1)/2].priority <= this.arr[i].priority
      ensures this.Valid()


  }
}