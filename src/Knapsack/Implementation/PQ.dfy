
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


    /* Lemma: proof that le is transitive */
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
    {
      LtWeakOrder();
    }

    static lemma LeReflexive()
      ensures forall x : Solution :: x.le(x)
    {
      LtIrreflexive();
    }


  }

  /* The following priority queue is implemented with a williams heap (binary heap) */
  class PriorityQueue {

    /* Atributes and constructor */

    var arr : array<Solution>
    var count : int  // current number of elements, if count == arr.Length, array must grow

    constructor ()
      ensures Valid()
      ensures fresh(arr)
      ensures Model() == multiset{}
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
    predicate IsEmpty()
      reads this, arr, set i | 0 <= i < arr.Length :: arr[i]
      requires Valid()
      ensures IsEmpty() == (Model() == multiset{})
    {
      count == 0
    }


    /* Predicate: true if s is the node with the minimum priority in the heap, i.e., no other node in the heap has a lower priority. */
    ghost predicate IsMin(s : Solution)
      reads this, arr, s, set i | i in Model(),  set i | 0 <= i < arr.Length :: arr[i]
      requires Valid()
      requires !IsEmpty()
    {
      && s in Model()// s belongs to the model
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
      ensures node in Model()
      ensures Model() == old(Model()) + multiset{node}
      ensures arr == old(arr) || fresh(arr)
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


    /* Method: this was the old swap method to verify float */
    method Swap(j : int, arr : array<Solution>)
      modifies arr
      requires 0 < j <= count - 1 < arr.Length
      requires forall i | 0 < i < count && i != j :: arr[(i-1)/2].le(arr[i])
      requires arr[j].lt(arr[(j-1)/2])
      requires j > 0 && 0 < 2*j+1 < count ==> arr[(j-1)/2].le(arr[2*j+1])
      requires j > 0 && 0 < 2*j+2 < count ==> arr[(j-1)/2].le(arr[2*j+2])

      ensures (j-1)/2 > 0 ==> forall i | 0 < i < count && (i-1)/2 == (j-1)/2 :: arr[((j-1)/2-1)/2].le(arr[i])
      ensures forall i | 0 < i < count && i != j && i != (j-1)/2 :: arr[i] == old(arr[i])
      ensures forall i | 0 < i < count && i != (j-1)/2 :: arr[(i-1)/2].le(arr[i])
      ensures multiset(arr[0..count]) == old(multiset(arr[0..count]))
    {

      arr[(j-1)/2], arr[j] := arr[j], arr[(j-1)/2]; // swap

      assert arr[(j-1)/2].lt(arr[j]);
      Solution.LtImpliesLe(arr[(j-1)/2], arr[j]);
      assert arr[(j-1)/2].le(arr[j]);

      forall i | 0 < i < count && i != (j-1)/2
        ensures arr[(i-1)/2].le(arr[i])
      {
        if i == j {
          // trivial
        }
        else if (i-1)/2 == (j-1)/2 { //i, j son hermanos
          assert arr[(i-1)/2].le(arr[j]);
          assert arr[j].le(arr[i]);
          Solution.LeTransitive();
          assert arr[(i-1)/2].le(arr[i]);
        }
        else { //i, j no son hermanos
          assert arr[i] == old(arr[i]);
          assert old(arr[(i-1)/2]).le(old(arr[i]));
          assert old(arr[(i-1)/2]).le(arr[i]);
        }
      }

      if ((j-1)/2 > 0) {
        forall i | 0 < i < count && (i-1)/2 == (j-1)/2
          ensures arr[((j-1)/2-1)/2].le(arr[i])
        {
          if (i != j) {
            assert arr[((j-1)/2-1)/2].le(arr[j]);
            assert arr[j].le(arr[i]);
            Solution.LeTransitive();
            assert arr[((j-1)/2-1)/2].le(arr[i]);
          }
        }
      }
    }


    /* Method: moves the last inserted node upward in the heap until the heap property is restored */
    method Float()
      modifies arr
      requires 0 < count <= arr.Length
      requires IsHeap(0, count - 1)
      ensures Valid()
      ensures Model() == old(multiset(arr[0..count-1]) + multiset{arr[count-1]})
    {
      var j := count - 1;
      while j > 0 && arr[j].lt(arr[(j-1)/2])
        invariant 0 <= j <= count - 1 < arr.Length
        invariant forall i | 0 < i < count && i != j :: arr[(i-1)/2].le(arr[i]) // todos excepto j son menores que su padre
        invariant j > 0 && 0 < 2*j+1 < count ==> arr[(j-1)/2].le(arr[2*j+1]) // el padre de j es menor que el hijo izquierdo de j
        invariant j > 0 && 0 < 2*j+2 < count ==> arr[(j-1)/2].le(arr[2*j+2]) // el padre de j es menor que el hijo derecho de j
        invariant multiset(arr[0..count]) == old(multiset(arr[0..count-1]) + multiset{arr[count-1]})
      {
        label L:

        arr[(j-1)/2], arr[j] := arr[j], arr[(j-1)/2]; // swap

        SwapFloatPreservesHeapProperty@L(j, arr);

        j := (j-1)/2;
      }
    }


    /* Method: deletes the element with the minimum priority of the heap */
    method DeleteMin()
      modifies this, arr
      requires Valid()
      requires !IsEmpty()
      ensures Valid()
      ensures Model() == old(Model()) - multiset{old(Min())}
      //ensures arr == old(arr) || fresh(arr)
    {
      var oldMin := arr[0];
      assert oldMin == old(Min()) == Min();

      arr[0] := arr[count - 1];
      assert multiset(arr[0..count]) == old(Model()) - multiset{old(arr[0])} + multiset{old(arr[count - 1])};
      assert multiset(arr[0..count]) == old(Model()) - multiset{old(Min())} + multiset{old(arr[count - 1])};

      count := count - 1;
      assert multiset(arr[0..count]) == old(Model()) - multiset{old(Min())};
      Sink();
      assert multiset(arr[0..count]) == old(Model()) - multiset{old(Min())};
      assert Model() == multiset(arr[0..count]);
    }


    /* Method: moves a node downward in the heap until the heap property is restored */
    method Sink()
      modifies arr
      requires 0 <= 0 <= count <= arr.Length
      requires forall i | 0 < i < count && (i-1)/2 != 0 :: arr[(i-1)/2].le(arr[i])
      ensures Valid()
      ensures multiset(arr[0..count]) == old(multiset(arr[0..count]))
    {
      var seguir := true;
      var j := 0;

      while (2*j+1 < count &&  ( arr[2*j+1].lt(arr[j]) || (2*j+2 < count && arr[2*j+2].lt(arr[j]))))//(if 2*j+2 < count && arr[2*j+2].le(arr[2*j+1]) then arr[2*j+2] else arr[2*j+1]).lt(arr[j])) // el bucle sigue si: j tiene hijos y el minimo de los dos es menor que j
         invariant 0 <= j <= count <= arr.Length
         invariant forall i | 0 < i < count  && (i-1)/2 != j :: arr[(i-1)/2].le(arr[i]) // todos excepto j y sus hijos, son menores que su padre
         invariant j > 0 && 2*j+1 < count ==> arr[(j-1)/2].le(arr[2*j+1]) // el padre de j es menor que el hijo izquierdo de j
         invariant j > 0 && 2*j+2 < count ==> arr[(j-1)/2].le(arr[2*j+2]) // el padre de j es menor que el hijo derecho de j
         invariant multiset(arr[0..count]) == old(multiset(arr[0..count]))
      {
        var m := if 2*j+2 < count && arr[2*j+2].le(arr[2*j+1]) then 2*j+2 else 2*j+1;

        assert j == (m-1)/2;
        SonIsSmaller(m, arr);
        label L:
        
        assert arr[m].lt(arr[j]) by {
          assert (arr[2*j+1].lt(arr[j]) || (2*j+2 < count && arr[2*j+2].lt(arr[j])));
           if (arr[2*j+1].lt(arr[j])) { 
            Solution.LeLtTransitive(arr[m],arr[2*j+1],arr[j]);
          }
          else {
            Solution.LeLtTransitive(arr[m],arr[2*j+2],arr[j]);
          }
        }

        arr[j], arr[m] := arr[m], arr[j]; // swap (j padre, m hijo)
        
        SwapSinkPreservesHeapProperty@L(j, m, arr);

        j := m;
      }   
    }


    /*Lemmas*/

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
        assert arr[0] in Model();
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
    

    lemma SonIsSmaller(m : int, arr : array<Solution>)
      requires 0 < m < count <= arr.Length
      requires m == if 2*((m-1)/2)+2 < count && arr[2*((m-1)/2)+2].le(arr[2*((m-1)/2)+1]) then 2*((m-1)/2)+2 else 2*((m-1)/2)+1
      ensures arr[m].le(arr[2*((m-1)/2) + 1])
      ensures 2*((m-1)/2) + 2 < count ==> arr[m].le(arr[2*((m-1)/2) + 2])
    {
      Solution.LtWeakOrder();
    }


    /* Lemma: proves that after swaping the value between j and his father (j-1)/2 in the float process, the heap property holds (excepting the father with its ancestors) */
    twostate lemma SwapFloatPreservesHeapProperty(j : int, arr : array<Solution>)
      requires 0 < j <= count - 1 < arr.Length

      // Precondiciones sobre el intercambio
      requires arr[j] == old(arr[(j-1)/2]) // actual hijo es lo que era el padre
      requires arr[(j-1)/2] == old(arr[j]) // actual padre es lo que era el hijo
      requires forall i | 0 <= i < count && i != j && i != (j-1)/2 :: arr[i] == old(arr[i]) // todos los elementos excepto j y su padre no han sido modificados

      // Precondiciones sobre la propiedad heap
      requires old(arr[j]).lt(old(arr[(j-1)/2])) // estado antiguo: el hijo era menor que su padre (no cumple heap)
      requires forall i | 0 < i < count && i != j :: old(arr[(i-1)/2]).le(old(arr[i])) // estado antiguo: todos excepto j eran menores que su padre
      requires arr[(j-1)/2].lt(arr[j]) // estado nuevo: el hijo es mayor que su padre (ya se hizo swap, si cumple heap)
      requires j > 0 && 0 < 2*j+1 < count ==> old(arr[(j-1)/2]).le(arr[2*j+1]) // el padre de j es menor que el hijo izquierdo de j
      requires j > 0 && 0 < 2*j+2 < count ==> old(arr[(j-1)/2]).le(arr[2*j+2]) // el padre de j es menor que el hijo derecho de j

      // Postcondiciones
      ensures forall i | 0 < i < count && i != (j-1)/2 :: arr[(i-1)/2].le(arr[i]) // todos los elementos cumplen la propiedad de heap a excepción del padre de j que seguirá flotando si se da el caso
      ensures (j-1)/2 > 0 ==> forall i | 0 < i < count && (i-1)/2 == (j-1)/2 :: arr[((j-1)/2-1)/2].le(arr[i]) // i,j que son hermanos cumplen la propiedad de heap con respecto a su abuelo, es decir, son mayores que el padre del padre de j
    {
      assert arr[(j-1)/2].lt(arr[j]);
      Solution.LtImpliesLe(arr[(j-1)/2], arr[j]); // x < y implies x <= y is true
      assert arr[(j-1)/2].le(arr[j]);

      forall i | 0 < i < count && i != (j-1)/2
        ensures arr[(i-1)/2].le(arr[i])
      {
        if i == j {}
        else if (i-1)/2 == (j-1)/2 { // i, j son hermanos (tienen mismo padre)
          assert arr[(i-1)/2].le(arr[j]); // x <= y
          assert arr[j].le(arr[i]); // y <= z
          Solution.LeTransitive(); // por transitividad:
          assert arr[(i-1)/2].le(arr[i]); // x <= z
        }
        else { // i, j no son hermanos: solo se ha modificado j y su padre
          assert arr[i] == old(arr[i]); // el resto de elementos i, permanecen igual que antes
          assert old(arr[(i-1)/2]).le(old(arr[i]));
          assert old(arr[(i-1)/2]).le(arr[i]); // por lo tanto, al no ser modificados, la propiedad de heap se sigue manteniendo
        }
      }

      if ((j-1)/2 > 0) {
        forall i | 0 < i < count && (i-1)/2 == (j-1)/2
          ensures arr[((j-1)/2-1)/2].le(arr[i])  // los hijos del padre de j (i,j), son mayores que el abuelo de j
        {
          if (i == j) {}
          else {
            assert arr[((j-1)/2-1)/2].le(arr[j]); // x <= y
            assert arr[j].le(arr[i]); // y <= z
            Solution.LeTransitive(); // por transitivdad
            assert arr[((j-1)/2-1)/2].le(arr[i]); // x <= z
          }
        }
      }
    }


    /* Lemma: proves that after swaping the value between m and his father j = (m-1)/2 in the sink process, the heap property holds (excepting the father with its ancestors) */
    twostate lemma SwapSinkPreservesHeapProperty(j:int, m : int, arr : array<Solution>)
      requires j == (m-1)/2 && (m == 2*j +1 || m == 2*j+2)
      requires 0 < m <= count - 1 < arr.Length
      requires 2*j+1 < count &&  ( old(arr[2*j+1]).lt(old(arr[j])) || (2*j+2 < count && old(arr[2*j+2]).lt(old(arr[j]))))

      // Precondiciones sobre el intercambio
      requires arr[m] == old(arr[j]) // actual hijo es lo que era el padre
      requires arr[j] == old(arr[m]) // actual padre es lo que era el hijo
      requires forall i | 0 <= i < count && i != m && i != j :: arr[i] == old(arr[i]) // todos los elementos excepto j y su padre no han sido modificados

      // Precondiciones sobre la propiedad heap
      requires old(arr[m]).lt(old(arr[j])) // estado antiguo: el hijo era menor que su padre (no cumple heap)
      requires old(arr[m]).le(old(arr[2*j+1])) // y menor o igual que su hermano (o <= que él mismo)
      requires 2*j+2 < count ==> old(arr[m]).le(old(arr[2*j + 2])) // si existe hijo derecho, m es menor que ese hijo derecho
      
      requires forall i | 0 < i < count && (i-1)/2 != j:: old(arr[(i-1)/2]).le(old(arr[i])) // estado antiguo: todos excepto j y sus hijos, son menores que su padre
      requires j > 0 ==> old(arr[(j-1)/2]).le(old(arr[m])) // m es mayor que su abuelo
      requires j > 0 && 0 < 2*j+2 < count ==> old(arr[(j-1)/2]).le(arr[2*j+2]) // el padre de j es menor que el hijo derecho de j

      // Postcondiciones
      ensures forall i | 0 < i < count && (i-1)/2 != m :: arr[(i-1)/2].le(arr[i]) // todos los elementos cumplen la propiedad de heap a excepción de m que podrá seguir hundiendose
    {
      assert arr[(m-1)/2].lt(arr[m]);
      Solution.LtImpliesLe(arr[(m-1)/2], arr[m]); // x < y implies x <= y is true
      assert arr[(m-1)/2].le(arr[m]);

      forall i | 0 < i < count && (i-1)/2 != m
        ensures arr[(i-1)/2].le(arr[i])
      {
        if (i == m) {}
        else if (i-1)/2 == (m-1)/2 { // i, m son hermanos (tienen mismo padre) // trivial
          assert arr[(i-1)/2].le(arr[m]);
          assert old(arr[m]).le(old(arr[2*((m-1)/2)+1]));
          assert arr[(i-1)/2].le(arr[i]);
        }
        else if (i == j) { // i es el padre de m
          if (j > 0) {
            assert arr[(i-1)/2] == arr[(j-1)/2];
            assert arr[(j-1)/2].le(arr[j]);
          }
        }
        else { // i no es ni j, ni m, ni hermano de m. No se ven afectados
          assert arr[i] == old(arr[i]); // i no se ha modificado
          assert old(arr[(i-1)/2]).le(old(arr[i])); // i cumplía con la propiedad heap
        }
      }
    }

  } // fin clase

} // fin modulo
