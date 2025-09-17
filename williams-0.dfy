/*

    This is Williams minimum heap implemented as a class
    Specified and verified by Ricardo Peña, January 2019

*/
class Williams_heap {
    var v: array<int>;
    var next: nat;
    //ghost var repr: set<object>;

    // It replaces the usual Valid() predicate. It specifies that v[j..next) is a minHeap
    /*
    predicate isHeap (j:nat) 
    requires 0 <= j <= v.Length
    reads this, v
    {
        this in repr && v in repr &&
        0 <= next <= v.Length && 
        forall i | 2*j+1 <= i < next :: v[(i-1)/2] <= v[i]
    }
    */

    constructor (size: nat) 
    //ensures isHeap(0) && v.Length == size && next == 0
    //ensures fresh (repr)
    {
        v := new int [size];
        next := 0;
        //repr := {this, v};
    }

    function method min(): int
    //reads repr
    //requires isHeap(0)
    requires next > 0
    {
        v[0]
    }

    method insert (val: int)
    //requires isHeap(0)
    requires next < v.Length
    //modifies repr
    //ensures isHeap(0) 
    //ensures next == old(next) + 1
    //ensures repr == old(repr) 
    //ensures v == old(v)
    {
        v[next] := val; next := next + 1;
        float ();
    }

    method float()
    //requires 0 < next <= v.Length
    //requires this in repr && v in repr;
    requires forall i | 0 < i < next-1 :: v[(i-1)/2] <= v[i]
    //modifies v
    //ensures repr == old(repr)
    //ensures isHeap(0)
    {
        var j := next-1;
        while j > 0 && v[(j-1)/2] > v[j] 
            //invariant 0 <= j <= next-1 < v.Length
            //invariant forall i | 0 < i < next :: i != j ==> v[(i-1)/2] <= v[i]
            //invariant j > 0 && 2*j+1< next ==> v[(j-1)/2] <= v[2*j+1] 
            //invariant j > 0 && 2*j+2< next ==> v[(j-1)/2] <= v[2*j+2]
        {
            v[(j-1)/2], v[j] := v[j], v[(j-1)/2];
            j := (j-1)/2;
        }
}

    method deleteMin ()
    //requires isHeap(0)
    requires 0 < next
    //modifies repr
    //ensures isHeap(0) 
    //ensures next == old(next) - 1
    //ensures repr == old(repr)
    {
        v[0] := v[next-1]; next := next - 1;
        sink (0, next);
    }

    // It sinks v[s] in a heap ending in v[l-1]
    method sink(s:nat, l:nat)
    requires 0 <= s <= l == next <= v.Length
    //requires this in repr && v in repr
    //requires forall i | 0 < i < next :: (i-1)/2 != s ==> v[(i-1)/2] <= v[i]
    //modifies v
    //ensures repr == old(repr)
    //ensures isHeap(s)
    {
        var j := s;
        while 2*j+1 < l 
            //invariant forall k | 2*s+1 <= k < l :: (k-1)/2 != j ==> v[(k-1)/2] <= v[k]
            //invariant j >= 2*s+1 && 2*j+1< l ==> v[(j-1)/2] <= v[2*j+1] 
            //invariant j >= 2*s+1 && 2*j+2< l ==> v[(j-1)/2] <= v[2*j+2]
        {
            var m: nat;
            if 2*j+2 < l && v[2*j+2] <= v[2*j+1] {
                m := 2*j+2;         // right son is smaller
            } else {
                m := 2*j+1;     // left son is smaller
            }				 		
            if v[j] > v[m] {
                v[j], v[m] := v[m], v[j];
                j  := m; 
            } else {   
                break;
            }								
        }
    }
}
method heapsort_with_extra_space (a: array<int>)
modifies a
{
    var queue := new Williams_heap(a.Length);
    var i := 0;
    while i < a.Length 
//        invariant queue.isHeap(0) 
//        invariant a.Length == queue.v.Length
//        invariant i == queue.next <= queue.v.Length 
//        invariant fresh(queue.repr)
    {
        queue.insert(a[i]);
        i := i + 1;
    }
    i := 0;
    while i < a.Length 
//        invariant queue.isHeap(0) 
//        invariant queue.next == a.Length - i
//        invariant fresh(queue.repr)
    {
        //assert queue.isHeap(0); 
        //assert queue.next > 0;
        a[i] := queue.min(); 
        queue.deleteMin();
        i := i + 1;
    }



// Exercise: add an observable  model function or model ghost field to the class, 
// write suitable postconditions in terms of the observable model, and prove 
// that array 'a' becomes sorted at the end of the second while loop
}