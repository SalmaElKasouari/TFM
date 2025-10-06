abstract module PQ {
  class Solution {
    var priority : real

    predicate Compare(other : Solution)
      reads this, other

  }

  /* The following priority queue is implemented with a williams heap (binary heap) */
  class PriorityQueue {

    /* Atributes and constructor */

    var arr : array<Solution>
    var count : int  // current number of elements, if count == arr.Length, array must grow

    constructor PriorityQueue(size: int)
      ensures Valid()
    {
      this.arr := new Solution[0];
      this.count := 0;
    }


    /* Predicates */

    /* Predicate: true if the segment [x, y) of the array satisfies the heap property*/
    ghost predicate IsHeap(x : int, y : int)
      reads this, this.arr, set i | 0 <= i < this.arr.Length :: arr[i]
    {
      && 0 <= x <= y <= arr.Length
      && (forall i | 2*x < i < y :: this.arr[(i-1)/2].priority <= this.arr[i].priority)
    }

    /* Predicate: true if the array satisfies the heap property */
    ghost predicate Valid()
      reads this, this.arr, set i | 0 <= i < this.arr.Length :: arr[i]
    {
      && IsHeap(0, this.count)
      && this.count <= this.arr.Length
    }


    /* Predicate: true if the heap has no elements */
    ghost predicate IsEmpty()
      reads this, this.arr, set i | 0 <= i < this.arr.Length :: arr[i]
      requires Valid()
    {
      Model() == {}
    }

    /* Predicate: true if m belongs to the model of the heap */
    ghost predicate IsInModel(node : Solution)
      reads this, this.arr, node, set i | 0 <= i < this.arr.Length :: arr[i]
      requires Valid()
    {
      node in Model()
    }


    /* Predicate: true if s is the node with the minimum priority in the heap, i.e., no other node in the heap has a lower priority. */
    ghost predicate IsMin(s : Solution)
      reads this, this.arr, s, set i | i in Model(),  set i | 0 <= i < this.arr.Length :: arr[i]
      requires Valid()
      requires !IsEmpty()
    {
      && IsInModel(s) // m belongs to the model
      && forall i : Solution | i in Model() :: s.priority <= i.priority // the priority of s is not greater than any element of the set
    }


    /* Functions */

    /* Function: returns the model of the heap */
    ghost function Model() : set<Solution>
      reads this, this.arr, set i | 0 <= i < this.arr.Length :: arr[i]
      requires Valid()
      ensures forall i : Solution | i in Model() :: (exists j | 0 <= j < this.count :: i == this.arr[j])
    {
      set j | 0 <= j < this.count :: this.arr[j]
    }

    /* Function: returns the element with the minimum priority in the heap */
    function Min() : Solution
      reads this, this.arr, set i | i in Model(), set i | 0 <= i < this.arr.Length :: arr[i]
      requires Valid()
      requires !IsEmpty()
      ensures Valid()
      //ensures IsMin(Min())
    {
      this.arr[0]
    }



    /* Methods */

    /* Method: returns the current number of elements in the heap */
    method Size() returns (c : int)
      requires Valid()
      ensures Valid()
      ensures forall i | 0 <= i < c == this.count :: IsInModel(this.arr[i])
      ensures forall s | s in Model() :: (exists i | 0 <= i < c == this.count :: this.arr[i] == s)
    {
      return this.count;
    }


    /* Method: inserts an element to the heap */
    method Insert(node : Solution)
      modifies this, this.arr
      requires Valid()
      ensures Valid()
      ensures IsInModel(node)
      ensures Model() == old(Model()) + {node}
      ensures !old(IsEmpty()) && node.priority > old(Min().priority) ==> Min() == old(Min())
    // {
    //   if (this.IsEmpty()) {
    //     var aux: array<Solution> := new Solution[1][node];
    //     this.arr := aux;
    //   }
    //   else if (this.count < this.arr.Length) { // array is not full
    //     this.arr[this.count] := node;
    //   }
    //   else { // array is full
    //     Grow();
    //     this.arr[this.count] := node;
    //   }
    //   this.count := this.count + 1;
    //   this.Float();
    // }


    /* Method: duplicates space of the heap */
    method Grow()
      modifies this, this.arr
      requires Valid()
      requires !IsEmpty()
      requires this.count <= this.arr.Length
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
      this.arr := aux;
    }


    /* Method: moves the last inserted node upward in the heap until the heap property is restored */
    method Float()
      modifies this.arr
      requires Valid()
      requires forall i | 0 < i < this.count - 1 :: this.arr[(i-1)/2].priority <= this.arr[i].priority
      ensures Valid()
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
      requires Valid()
      requires !IsEmpty()
      ensures Valid()
      ensures !IsInModel(old(Min()))
      ensures Model() == old(Model()) - {old(Min())}
    // {
    //   this.arr[0] := this.arr[this.count - 1];
    //   this.count := this.count - 1;
    //   Sink(0, this.count);      
    // }


    /* Method: moves a node downward in the heap until the heap property is restored */
    method Sink(s : nat, l : nat)
      modifies this.arr
      requires 0 <= s <= l == this.count <= arr.Length
      requires forall i | 0 < i < this.count && (i-1)/2 != s :: this.arr[(i-1)/2].priority <= this.arr[i].priority
      ensures Valid()


  }
}