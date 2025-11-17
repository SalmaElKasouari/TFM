abstract module PQ {

  class Solution {

    /* Predicates */

    /* 
    Predicate: defines the non-strict ordering (<=) between two solutions. Returns true if this solution 
    has a priority less than or equal to the other. This predicate is defined in 
    terms of 'lt', so that le(other) <==> Not(other.lt(this)).
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
    Predicate: incomparable property
    */
    predicate eq (y : Solution)
      reads this, y
    {
      !lt(y) && !y.lt(this)
    }


    /* Lemas */

    /* Lemma: proof that lt is irreflexive */
    static lemma LtIrreflexive()
      ensures forall x : Solution :: !x.lt(x)


    /* Lemma: proof that lt is antisymmetric */
    static lemma LtAntisymmetric()
      ensures forall x : Solution, y : Solution :: x.lt(y) ==> !y.lt(x)


    /* Lemma: proof that lt is transitive */
    static lemma LtTransitive()
      ensures forall x : Solution, y : Solution, z : Solution :: x.lt(y) && y.lt(z) ==> x.lt(z)


    /* Lemma: proof that le is transitive */ // NUEVOOOOOOOOOOOOOOOOOOOOOOOOO, necesario para demo en swap
    static lemma LeTransitive()
      ensures forall x : Solution, y : Solution, z : Solution :: x.le(y) && y.le(z) ==> x.le(z)


    /* Lemma: proof that lt is transitive */
    static lemma LeLtTransitive(x : Solution, y : Solution, z : Solution)
      requires x.le(y) && y.lt(z)
      ensures x.lt(z)
    {
      Solution.LtWeakOrder();
      assert x.le(z);
      if(!x.lt(z)){
        assert z.le(x);
        assert x.eq(z) && x.eq(y) && y.eq(z);
        assert false;
      }
    }

    /* Lemma: proof that lt satisfies transitive incomparability */
    static lemma LtTransitiveIncomparability()
      ensures forall x : Solution, y : Solution, z : Solution :: x.eq(y) && y.eq(z) ==> x.eq(z)


    /* Lemma: proof that lt satisfies weak order */
    static lemma LtWeakOrder()
      ensures forall x : Solution :: !x.lt(x)
      ensures forall x : Solution, y : Solution :: x.lt(y) ==> !y.lt(x)
      ensures forall x : Solution, y : Solution, z : Solution :: x.lt(y) && y.lt(z) ==> x.lt(z)
      ensures forall x : Solution, y : Solution, z : Solution :: x.eq(y) && y.eq(z) ==> x.eq(z)
    {
      LtIrreflexive();
      LtAntisymmetric();
      LtTransitive();
      LtTransitiveIncomparability();
    }

    static lemma LtImpliesLe(x : Solution, y : Solution)
      requires x.lt(y) // x < y
      ensures x.le(y) // x <= y

  }

  /* The following priority queue is implemented with a williams heap (binary heap) */
  class PriorityQueue {

    /* Atributes and constructor */

    var arr : array<Solution>
    var count : int  // current number of elements, if count == arr.Length, array must grow

    constructor PriorityQueue(size: int)
      ensures Valid()
    {
      arr := new Solution[0];
      count := 0;
    }


    /* Predicates */

    /* Predicate: true if the segment [x, y) of the array satisfies the heap property*/
    ghost predicate IsHeap(x : int, y : int)
      reads this, arr, set i | 0 <= i < arr.Length :: arr[i]
    {
      && 0 <= x <= y <= arr.Length
      && (forall i | 2*x < i < y :: arr[(i-1)/2].le(arr[i]))
    }

    /* Predicate: true if the array satisfies the heap property */
    ghost predicate Valid()
      reads this, arr, set i | 0 <= i < arr.Length :: arr[i]
    {
      && IsHeap(0, count)
      && 0 <= count <= arr.Length
    }


    /* Predicate: true if the heap has no elements */
    ghost predicate IsEmpty()
      reads this, arr, set i | 0 <= i < arr.Length :: arr[i]
      requires Valid()
    {
      Model() == multiset{}
    }

    /* Predicate: true if m belongs to the model of the heap */
    ghost predicate IsInModel(node : Solution)
      reads this, arr, node, set i | 0 <= i < arr.Length :: arr[i]
      requires Valid()
      //requires 0 <= count <= arr.Length
    {
      node in Model()
    }


    /* Predicate: true if s is the node with the minimum priority in the heap, i.e., no other node in the heap has a lower priority. */
    ghost predicate IsMin(s : Solution)
      reads this, arr, s, set i | i in Model(),  set i | 0 <= i < arr.Length :: arr[i]
      requires Valid()
      requires !IsEmpty()
    {
      && IsInModel(s) // m belongs to the model
      && forall i : Solution | i in Model() :: s.le(i) // the priority of s is not greater than any element of the set
    }


    /* Functions */

    /* Function: returns the model of the heap */
    ghost function Model() : multiset<Solution>
      reads this, arr, set i | 0 <= i < arr.Length :: arr[i]
      requires Valid()
    {
      multiset(arr[0..count])
    }


    lemma BelongsToArray(i : Solution)
      requires Valid()
      requires i in Model()
      ensures (exists j | 0 <= j < count :: arr[j] == i)
    {}


    lemma FirstIsMin()
      requires Valid()
      requires !IsEmpty()
      ensures IsMin(arr[0])
    {
      if (!IsMin(arr[0])) {
        assert IsInModel(arr[0]);
        assert exists s : Solution | s in Model() :: s.lt(arr[0]);

        // s es la solucion que es menor que arr[0]
        var s :| s in Model() && s.lt(arr[0]);
        BelongsToArray(s);
        Solution.LtIrreflexive();

        // j es la posicion de esa solucion s
        var j :| 1 <= j < count && arr[j] == s && s.lt(arr[0]);
        while j != 0
          invariant 0 <= j < count
          invariant arr[j].lt(arr[0])
        {
          Solution.LeLtTransitive(arr[(j-1)/2], arr[j], arr[0]);
          assert arr[(j-1)/2].le(arr[j]);
          assert arr[(j-1)/2].lt(arr[0]);
          j := (j-1)/2;
        }
      }
    }



    /* Function: returns the element with the minimum priority in the heap */
    function Min() : Solution
      reads this, arr, set i | i in Model(), set i | 0 <= i < arr.Length :: arr[i]
      requires Valid()
      requires !IsEmpty()
      ensures Valid()
      ensures IsMin(Min())
    {
      FirstIsMin();
      arr[0]
    }



    /* Methods */

    /* Method: returns the current number of elements in the heap */
    method Size() returns (c : int)
      requires Valid()
      ensures Valid()
      ensures c == |Model()|
    {
      return count;
    }


    /* Method: inserts an element to the heap */
    method Insert(node : Solution)
      modifies this, arr
      requires Valid()
      ensures Valid()
      ensures IsInModel(node)
      ensures Model() == old(Model()) + multiset{node}
    {
      if (count == 0) { // array is empty
        var aux: array<Solution> := new Solution[1][node];
        arr := aux;
        count := count + 1;
      }
      else if (count < arr.Length) { // array is not full
        arr[count] := node;
        count := count + 1;
        Float();
      }
      else { // array is full
        Grow();
        arr[count] := node;
        count := count + 1;
        Float();
      }
    }


    /* Method: duplicates space of the heap */
    method Grow()
      modifies this, arr
      requires Valid()
      requires !IsEmpty()
      ensures count == old(count) // the number of elements does not change in this method. The Method Insert increases it
      ensures arr.Length > old(arr.Length) // the length of the array increases
      ensures fresh(arr) // is new in memory
      ensures arr[0..count] == old(arr[0..count]) // the elements that were already in the array are preserved
    {
      // allocate new memory
      var last := arr[count-1];
      var aux: array<Solution> := new Solution[2 * arr.Length] (_ => last);

      // copy
      var i := 0;
      while i < count
        decreases count-i
        invariant 0 <= i <= count <= arr.Length < aux.Length && count == old(count)
        invariant aux[0..i] == arr[0..i]
        invariant arr[0..count] == old(arr[0..count])
      {
        aux[i] := arr[i];
        i := i + 1;
      }
      assert aux[0..count] == arr[0..count] == old(arr[0..count]);
      arr := aux;
    }

    // lemma ForallInst(i : int, j : int, arr : array<Solution>)    NO SE USA
    //   requires 0 < j <= count - 1 < arr.Length
    //   requires forall k | 0 < k < count && k != j :: arr[(k-1)/2].le(arr[k])
    //   requires 0 < i < count && i != j
    //   ensures arr[(i-1)/2].le(arr[i])
    // {}

    method Swap(j : int, arr : array<Solution>)
      modifies arr
      requires 0 < j <= count - 1 < arr.Length
      requires forall i | 0 < i < count && i != j :: arr[(i-1)/2].le(arr[i])
      requires arr[j].lt(arr[(j-1)/2])
      ensures forall i | 0 < i < count && i != j && i != (j-1)/2 :: arr[i] == old(arr[i])
      ensures forall i | 0 < i < count && i != (j-1)/2 :: arr[(i-1)/2].le(arr[i])
      ensures multiset(arr[0..count]) == old(multiset(arr[0..count-1]) + multiset{arr[count-1]})
    {
      var value_oldj := arr[j];
      var value_oldparent := arr[(j-1)/2]; // 5

      arr[(j-1)/2], arr[j] := arr[j], arr[(j-1)/2]; // swap
      assert arr[(j-1)/2].lt(arr[j]);  // sabe que x < y
      Solution.LtImpliesLe(arr[(j-1)/2], arr[j]);
      assert arr[(j-1)/2].le(arr[j]);  // lemma (x < y) --> x <= y

      forall i | 0 < i < count && i != (j-1)/2
        ensures arr[(i-1)/2].le(arr[i])
      {
        if i == j {
          // trivial
        }
        else if (i-1)/2 == (j-1)/2 { // i, j son hermanos
          assert i != j;

          assert arr[(j-1)/2].le(arr[j]);
          assert arr[(i-1)/2].le(arr[j]); // 4 <= 5
          assert arr[j].le(arr[i]); // 5 <= a[i]

          Solution.LeTransitive(); // 4 <= 5 y 5 <= i --> 4 <= i
          assert arr[(i-1)/2].le(arr[i]);
        }
        else {
          assert i != j;
          assert (i-1)/2 != (j-1)/2;
          assert i != (j-1)/2;
          assert arr[i] == old(arr[i]);
          assert old(arr[(i-1)/2]).le(old(arr[i]));
          assert old(arr[(i-1)/2]).le(arr[i]);

          if (j != (i-1)/2) { // j el padre de i, osea que es modificado
            assert arr[(i-1)/2] == old(arr[(i-1)/2]);
          }
          else { // j no es el padre de i --> el padre de i no es modificado
            assert old(arr[(i-1)/2]) == value_oldj;
            assert old(arr[(i-1)/2]) == arr[(j-1)/2];
            assert old(arr[(i-1)/2]).le(arr[i]); // 1 <= 4
            assert old(arr[j]).le(arr[i]); // 1 <= 4
            assert value_oldj == old(arr[j]) == arr[(j-1)/2];

            assert value_oldj.le(arr[i]);
            assert arr[j] == arr[(i-1)/2];
            assert arr[(j-1)/2].le(arr[j]); // 1 <= 2
            assert arr[(j-1)/2].le(arr[i]); // 1 <= 4

            assert value_oldparent == old(arr[(j-1)/2]);

            // quiero 2 <= 4
            assume false;
          }

        }
      }
    }


    /* Method: moves the last inserted node upward in the heap until the heap property is restored */
    method Float()
      modifies arr
      requires 0 < count <= arr.Length
      requires IsHeap(0, count - 1);
      ensures Valid()
      ensures Model() == old(multiset(arr[0..count-1]) + multiset{arr[count-1]})
    {
      var j := count - 1;
      while j > 0 && arr[j].lt(arr[(j-1)/2])
        invariant 0 <= j <= count - 1 < arr.Length
        invariant forall i | 0 < i < count && i != j :: arr[(i-1)/2].le(arr[i])
        invariant multiset(arr[0..count]) == old(multiset(arr[0..count-1]) + multiset{arr[count-1]})
      {
        Swap(j, arr);
        j := (j-1)/2;
      }

      if j > 0 {
        assert arr[(j-1)/2].le(arr[j]);
      }
    }



    /* Method: deletes the element with the minimum priority of the heap */
    method DeleteMin()
      modifies this, arr
      requires Valid()
      requires !IsEmpty()
      ensures Valid()
      ensures Model() == old(Model()) - multiset{old(Min())}
    {
      var oldMin := arr[0];
      assert oldMin == old(Min()) == Min();

      arr[0] := arr[count - 1];
      assert multiset(arr[0..count]) == old(Model()) - multiset{old(arr[0])} + multiset{old(arr[count - 1])};
      assert multiset(arr[0..count]) == old(Model()) - multiset{old(Min())} + multiset{old(arr[count - 1])};

      count := count - 1;
      assert multiset(arr[0..count]) == old(Model()) - multiset{old(Min())};
      Sink(0, count);
      assert multiset(arr[0..count]) == old(Model()) - multiset{old(Min())};
      assert Model() == multiset(arr[0..count]);
    }


    /* Method: moves a node downward in the heap until the heap property is restored */
    method Sink(s : nat, l : nat)
      modifies arr
      requires 0 <= s <= l == count <= arr.Length
      requires forall i | 0 < i < count && (i-1)/2 != s :: arr[(i-1)/2].le(arr[i])
      ensures Valid()
      ensures multiset(arr[0..count]) == old(multiset(arr[0..count])) // equivale a Model() == old(Model()), lo q pasa q no se puede invocar a old(Model()) porq arr no es un heap al entrar al método, Sink lo hace un heap
    {
      var j := s;
      while (2*j+1 < l)
        //invariant forall k | 0 < k < l && (k - 1)/2 != j :: arr[(k-1)/2].le(arr[k])
        invariant multiset(arr[0..count]) == old(multiset(arr[0..count]))
      {
        var m : nat;
        if (2*j+2 < l && arr[2*j+2].le(arr[2*j+1])) {
          m := 2*j+2;  // right son is smaller
        }
        else {
          m := 2*j+1;  // left son is smaller
        }
        if (arr[m].lt(arr[j])) {
          arr[j], arr[m] := arr[m], arr[j];
          assert arr[j].lt(arr[m]);
          j := m;
        }
        else {
          break;
        }
      }
      assume (forall i | 0 < i < count :: arr[(i-1)/2].le(arr[i]));
    }


  } // fin clase

} // fin modulo


