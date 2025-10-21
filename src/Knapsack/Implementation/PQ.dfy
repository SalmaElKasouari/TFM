abstract module PQ {

  class Solution {

    /* Predicates */

    /* 
    Predicate: defines the non-strict ordering (<=) between two solutions. Returns true if this solution 
    has a priority less than or equal to the other. This predicate is defined in 
    terms of 'lt', so that this.le(other) <==> Not(other.lt(this)).
    */
    predicate le (other : Solution)
      reads this, other
    {
      !other.lt(this)
    }

    /* 
    Predicate: defines the strict order relation between two solutions.
    Must be implemented by refined modules to define the comparison criterion.
    */
    predicate lt (other: Solution)
      reads this, other


    /* 
    Predicate: irreflexive property
    */
    predicate Irreflexive (x : Solution)
      reads x
    {
      !x.lt(x)
    }


    /* 
    Predicate: Asymmetric property
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
    Predicate: incomparable property
    */
    predicate Incomparable (x : Solution, y : Solution)
      reads x, y
    {
      !x.lt(y) && !y.lt(x)
    }

    /* 
    Predicate: transitive incomparability property
    */
    predicate TransitiveIncomparability (x : Solution, y : Solution, z : Solution)
      reads x, y, z
    {
      Incomparable(x,y) && y.Incomparable(y,z) ==> Incomparable(x,z)
    }

    /* 
    Predicate: weak order property
    */
    predicate WeakOrder(x : Solution, y : Solution, z : Solution)
      reads x, y, z
    {
      && Irreflexive(x)
      && Asymmetric(x,y)
      && Transitive(x, y, z)
      && TransitiveIncomparability(x, y, z)
    }

    /* Lemas */

    /* Lemma: proof that lt is irreflexive */
    lemma LtIrreflexive()
      ensures forall x : Solution :: Irreflexive(x)


    /* Lemma: proof that lt is asymmetric */
    lemma LtAsymmetric()
      ensures forall x, y : Solution :: Asymmetric(x, y)


    /* Lemma: proof that lt is transitive */
    lemma LtTransitive()
      ensures forall x, y, z : Solution :: Transitive(x, y, z)


    /* Lemma: proof that lt satisfies transitive incomparability */
    lemma LtTransitiveIncomparability()
      ensures forall x, y, z : Solution :: TransitiveIncomparability(x, y, z)


    /* Lemma: proof that lt satisfies weak order */
    lemma LtWeakOrder()
      ensures forall x, y, z: Solution :: WeakOrder(x, y, z)

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
      reads this, this.arr, set i | 0 <= i < this.arr.Length :: this.arr[i]
    {
      && 0 <= x <= y <= arr.Length
      && (forall i | 2*x < i < y :: this.arr[(i-1)/2].le(this.arr[i]))
    }

    /* Predicate: true if the array satisfies the heap property */
    ghost predicate Valid()
      reads this, this.arr, set i | 0 <= i < this.arr.Length :: this.arr[i]
    {
      && IsHeap(0, this.count)
      && 0 <= this.count <= this.arr.Length
    }


    /* Predicate: true if the heap has no elements */
    ghost predicate IsEmpty()
      reads this, this.arr, set i | 0 <= i < this.arr.Length :: this.arr[i]
      requires Valid()
    {
      Model() == multiset{}
    }

    /* Predicate: true if m belongs to the model of the heap */
    ghost predicate IsInModel(node : Solution)
      reads this, this.arr, node, set i | 0 <= i < this.arr.Length :: this.arr[i]
      requires 0 <= this.count <= this.arr.Length
    {
      node in Model()
    }


    /* Predicate: true if s is the node with the minimum priority in the heap, i.e., no other node in the heap has a lower priority. */
    ghost predicate IsMin(s : Solution)
      reads this, this.arr, s, set i | i in Model(),  set i | 0 <= i < this.arr.Length :: this.arr[i]
      requires Valid()
      requires !IsEmpty()
    {
      && IsInModel(s) // m belongs to the model
      && forall i : Solution | i in Model() :: s.le(i) // the priority of s is not greater than any element of the set
    }


    /* Functions */

    /* Function: returns the model of the heap */
    ghost function Model() : multiset<Solution>
      reads this, this.arr, set i | 0 <= i < this.arr.Length :: this.arr[i]
      requires 0 <= this.count <= this.arr.Length
      ensures forall i : Solution | i in Model() :: (exists j | 0 <= j < this.count :: i == this.arr[j])
    {
      multiset(arr[0..this.count])
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
      ensures c == |Model()|
    {
      return this.count;
    }


    /* Method: inserts an element to the heap */
    method Insert(node : Solution)
      modifies this, this.arr
      requires Valid()
      ensures Valid()
      ensures IsInModel(node)
      ensures Model() == old(Model()) + multiset{node}
      //ensures !old(IsEmpty()) && old(Min()).lt(node) ==> Min() == old(Min()) no es necesario
    {
      if (this.count == 0) { // array is empty
        var aux: array<Solution> := new Solution[1][node];
        this.arr := aux;
        this.count := this.count + 1;
      }
      else if (this.count < this.arr.Length) { // array is not full
        this.arr[this.count] := node;
        this.count := this.count + 1;
        Float();
      }
      else { // array is full
        Grow();
        this.arr[this.count] := node;
        this.count := this.count + 1;
        Float();
      }
    }


    /* Method: duplicates space of the heap */
    method Grow()
      modifies this, this.arr
      requires Valid()
      requires !IsEmpty()
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
      requires 0 < this.count <= this.arr.Length
      requires forall i | 0 < i < this.count - 1 :: this.arr[(i-1)/2].le(this.arr[i])
      ensures Valid()
      ensures Model() == old(Model())
    // {
    //     var j := this.count - 1;
    //     while j > 0 && this.arr[j].lt(this.arr[(j-1)/2])
    //         invariant 0 <= j <= this.count - 1 < this.arr.Length
    //         invariant forall i | 0 < i < this.count && i != j :: this.arr[(i-1)/2].le(this.arr[i])
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
      //ensures Model() == old(Model()) - multiset{old(Min())}
    {
      var oldModel := old(Model());
      var oldMin := old(Min());

      this.arr[0] := this.arr[this.count - 1];
      this.count := this.count - 1;
      Sink(0, this.count);
    }


    /* Method: moves a node downward in the heap until the heap property is restored */
    method Sink(s : nat, l : nat)
      modifies this.arr
      requires 0 <= s <= l == this.count <= arr.Length
      requires forall i | 0 < i < this.count && (i-1)/2 != s :: arr[(i-1)/2].le(arr[i])
      ensures Valid()
      //ensures Model() == old(Model())
    {
      var j := s;
      while (2*j+1 < l)
        // invariant forall k | 0 < k < l && (k - 1)/2 != j :: this.arr[(k-1)/2].le(this.arr[k])
        // invariant j >= 2*s+1 && 2*j+1< l ==> this.arr[(j-1)/2].le(this.arr[2*j+1])
        // invariant j >= 2*s+1 && 2*j+2< l ==> this.arr[(j-1)/2].le(this.arr[2*j+2])
      {
        var m : nat;
        if (2*j+2 < l && this.arr[2*j+2].le(this.arr[2*j+1])) {
          m := 2*j+2;  // right son is smaller
        }
        else {
          m := 2*j+1;  // left son is smaller
        }
        if (this.arr[m].lt(this.arr[j])) {
          this.arr[j], this.arr[m] := this.arr[m], this.arr[j];
          j := m;
        }
        else {
          break;
        }
      }

      assert Valid() by {
        assert 0 <= this.count <= this.arr.Length;
        assert IsHeap(0, this.count) by {
          assert 0 <= 0 <= this.count <= arr.Length;
          assume (forall i | 2*0 < i < this.count :: this.arr[(i-1)/2].le(this.arr[i]));
        }
      }
    }
  }
}


