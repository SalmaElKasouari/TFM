include "ValuePQ.dfy"
import opened ValuePQ

/* Predicado: comprueba que una secuencia este ordenada en orden creciente. */
predicate Sorted(v : seq<real>)
{
  forall i | 0 <= i < |v| - 1 :: v[i] <= v[i + 1]
}

/* Predicado: los valores que están en la cola coinciden con los valores de v (también se aplica a las ocurrencias) y viceversa. */
ghost predicate SameValues(v : array<real>,pq:PriorityQueue, i:int)
  reads v, pq, pq.arr, set i | 0 <= i < pq.arr.Length :: pq.arr[i]
  requires 0 <= i <= v.Length
  requires pq.Valid() //&& |pq.Model()| == v.Length
  requires multiset{pq} !! multiset{pq.arr as object}  !! pq.Model()
{
  && (forall e | e in multiset(v[..i]) :: e in Values(pq.Model()) 
  && multiset(v[..i])[e] == Values(pq.Model())[e]) 
  && (forall e | e in Values(pq.Model()) :: e in multiset(v[..i]))
  && Values(pq.Model()).Keys == set x <- v[..i]
}


/* Predicado: comprueba que:
  - todo lo que está en w viene de v
  - todo lo que estaba en v esta en w o en la cola
  - la multiplicidad es la suma de w mas la de la cola (pero con distinción de casos)
*/
opaque ghost predicate SumValues(v : array<real>,w:array<real>,pqModel:multiset<Solution>, i:int)
  reads v, w, set s <- pqModel
  requires 0 <= i <= v.Length == w.Length
{
  && (forall e | e in multiset(v[..]) :: (e in multiset(w[..i]) || e in Values(pqModel)))
  && (forall e | e in multiset(w[..i]) :: e in multiset(v[..]))

  && forall e | e in multiset(v[..]) ::
    if  e in Values(pqModel) && e in multiset(w[..i]) then multiset(v[..])[e] == Values(pqModel)[e]  + multiset(w[..i])[e]
    else if e in Values(pqModel) && e !in multiset(w[..i]) then  multiset(v[..])[e] == Values(pqModel)[e]
    else multiset(v[..])[e] == multiset(w[..i])[e]

}


lemma OneMoreSorted(v : seq<real>,e:real)
  requires Sorted(v)
  requires forall x | x in v :: x <= e
  ensures Sorted(v+[e])
{ 
  if v ==[]  {}
  else { assert v[|v|-1] in v && v[|v|-1] <= e;}
}

ghost function Values(pq : multiset<Solution>) : map<real,nat>
  reads pq
{
  map x | x in (set s <- pq :: s.value) :: |(set ss <- pq | ss.value == x)|
}

lemma AddOne(m : multiset<Solution>,s:Solution)
  requires s !in m
  ensures if s.value !in  Values(m) then
            Values(m+multiset{s}) == Values(m)[s.value:=1]
          else Values(m+multiset{s}) == Values(m)[s.value:=Values(m)[s.value]+1]
  ensures Values(m+multiset{s}).Keys == Values(m).Keys+{s.value}
{
  if s.value !in  Values(m) {
    var ms := m+multiset{s};
    assert Values(ms) == map x | x in (set s <- ms :: s.value) :: |(set ss <- ms  | ss.value == x)|;
    //assert Values(m+multiset{s}).Keys == Values(m).Keys + {s.value};
    //assert Values(m+multiset{s}).Keys == Values(m)[s.value:=1].Keys;
    forall e | e in Values(m+multiset{s})
      ensures Values(m+multiset{s})[e] == Values(m)[s.value:=1][e]
    {
      if (e == s.value) {
        assert (set ss <-ms  | ss.value == s.value) == {s};
      }
      else {
        assert (set ss <-ms  | ss.value == e) == (set ss <-m  | ss.value == e);
      }

    }
  }
  else { //s.value in Values(m)
    var ms := m + multiset{s};
    assert Values(ms) == map x | x in (set s <- ms :: s.value) :: |(set ss <-ms  | ss.value == x)|;
    //assert Values(m+multiset{s}).Keys == Values(m)[s.value:=Values(m)[s.value]+1].Keys;
    forall e | e in Values(m+multiset{s})
      ensures Values(m+multiset{s})[e] == Values(m)[s.value:=Values(m)[s.value]+1][e]
    {
      if (e == s.value) {
        assert (set ss <-ms  | ss.value == s.value) == (set ss <-m  | ss.value == s.value) + {s};
        //assert |(set ss <-ms  | ss.value == s.value)| == |(set ss <-m  | ss.value == s.value)| + 1;
        assert Values(m+multiset{s})[s.value] == Values(m)[s.value]+1;
      }
      else {
        assert (set ss <-ms  | ss.value == e) == (set ss <-m  | ss.value == e);
      }
    }
  }
}


lemma AddValues(m : multiset<Solution>,s:Solution)
  requires s !in m
  ensures if s.value !in  Values(m) then Values(m+multiset{s})[s.value] == 1
          else  Values(m+multiset{s})[s.value] ==  Values(m)[s.value] + 1
  ensures forall e | e in Values(m) && e != s.value ::  Values(m+multiset{s})[e] ==  Values(m)[e]
{
  AddOne(m,s);
}

lemma notEmpty(s:Solution,ss:set<Solution>)
  requires s in ss
  ensures ss != {}
{}

lemma sizeSet1(s:Solution,m:multiset<Solution>)
  requires s in m && m[s] == 1
  requires s.value in Values(m-multiset{s}).Keys
  ensures (set ss <- m-multiset{s} | ss.value == s.value) == (set ss <- m | ss.value == s.value) - {s}
  ensures |(set ss <- m-multiset{s} | ss.value == s.value)| == |(set ss <- m | ss.value == s.value)| - 1
{}

lemma sizeSet2(s:Solution,m:multiset<Solution>)
  requires s in m && m[s] == 1
  ensures forall e | e in Values(m) && e != s.value :: e in (set r <- m :: r.value)
  ensures forall e | e in Values(m) && e != s.value ::  (set ss <- m-multiset{s} | ss.value == e) == (set ss <- m | ss.value == e)
  ensures forall e | e in Values(m) && e != s.value ::  |set ss <- m-multiset{s} | ss.value == e| == |set ss <- m | ss.value == e|
{}

lemma DelOne(m : multiset<Solution>,s:Solution)
  requires s in m
  requires m[s]==1
  ensures s.value in Values(m) && Values(m)[s.value]>0
  ensures s.value in Values(m-multiset{s}).Keys ==> Values(m-multiset{s})[s.value] ==  Values(m)[s.value] - 1
  ensures forall e | e in Values(m) && e != s.value ::  e in Values(m-multiset{s}) && Values(m-multiset{s})[e]==  Values(m)[e]
  ensures if Values(m)[s.value]> 1 then Values(m-multiset{s}).Keys == Values(m).Keys
          else Values(m-multiset{s}).Keys == Values(m).Keys-{s.value}
{
  assert s.value in (set r <- m  :: r.value);
  assert s in (set ss <- m | ss.value == s.value);
  notEmpty(s,(set ss <- m | ss.value == s.value));
  assert (set ss <- m | ss.value == s.value) != {};
  assert |(set ss <- m | ss.value == s.value)| > 0;
  var ms := m-multiset{s};
  assert Values(m-multiset{s})==Values(ms);

  if s.value in Values(ms).Keys {
    sizeSet1(s,m);
    assert (set ss <- m-multiset{s} | ss.value == s.value) == (set ss <- ms | ss.value == s.value);
  }

  if Values(m)[s.value] > 1 {
    assert |(set ss <- m | ss.value == s.value)| > 1;
    if s.value !in (set r <- ms  :: r.value) { 
      assert (set ss <- m | ss.value == s.value) == {s};
      assert false;
    }
    assert s.value in (set r <- ms  :: r.value);
    assert s.value in Values(ms).Keys;
    sizeSet1(s,m);
    assert Values(m-multiset{s}).Keys == Values(m).Keys;
  }
  else {
    assert |(set ss <- m | ss.value == s.value)| == 1;
    if s.value in (set r <- ms  :: r.value) {
      var s' :| s' in ms && s'.value == s.value && s' in (set ss <- ms | ss.value == s.value);
      notEmpty(s',(set ss <- ms | ss.value == s.value));
      assert |(set ss <- ms | ss.value == s.value)|>0;
      assert false;
    }
    assert Values(m-multiset{s}).Keys == Values(m).Keys-{s.value};
  }

  forall e | e in Values(m) && e != s.value
    ensures e in Values(m-multiset{s}) && Values(m-multiset{s})[e] ==  Values(m)[e]
  {
    sizeSet2(s,m);
    assert (set ss <- m-multiset{s} | ss.value == e) == (set ss <- ms | ss.value == e);
    assert e in Values(m-multiset{s});
    assert |set ss <- m-multiset{s} | ss.value == e| == |set ss <- m | ss.value == e|;
  }
}


/* 
Lema: los valores del vector resultado w son los mismos que los valores del vector de entrada v.
//
Propósito: demostrar ExtractPQ
//
Verificación: usando una demostración forall
*/
lemma FinalValues(v : array<real>, w:array<real>, pq:PriorityQueue)
  requires v.Length == w.Length
  requires pq.Valid() && |pq.Model()| == 0
  requires multiset{pq} !! multiset{pq.arr as object}  !! pq.Model()
  requires SumValues(v,w,pq.Model(),w.Length)
  ensures multiset(w[..]) == multiset(v[..])
{
  reveal SumValues;
  assert pq.Model() == multiset{};
  assert Values(pq.Model()).Keys == {};
  assert forall e | e in multiset(v[..]) :: e !in Values(pq.Model()) && e in  multiset(w[..]);

  forall e | e in multiset(v[..])
    ensures multiset(v[..])[e] == multiset(w[..])[e]
  {
    assert e !in Values(pq.Model()) && e in  multiset(w[..]);
    assert multiset(v[..])[e] == multiset(w[..w.Length])[e];
    assert w[..] == w[..w.Length];
  }

  assert multiset(v[..]) <= multiset(w[..]);
  assert forall e | e in multiset(w[..]):: e in multiset(v[..]);
  // assert multiset(w[..]) <= multiset(v[..]);
}


/* 
Lema: restaura el invariante sumValues.
//
Propósito: verificar ExtractPQ.
//
Verificación: usando el lema DelOne.
*/
lemma Restore (oldpqModel:multiset<Solution>, pqModel:multiset<Solution>, m:Solution, w:array<real>, v:array<real>, i:int)
  requires w.Length == v.Length
  requires 0 <= i < w.Length
  requires m in oldpqModel //&& m.value in Values(oldpqModel) && Values(oldpqModel)[m.value]>0
  requires pqModel + multiset{m} == oldpqModel
  requires m !in pqModel && w[i] == m.value
  requires Values(oldpqModel).Keys <= set x <- v[..]

  requires SumValues(v,w,oldpqModel,i)
  ensures SumValues(v,w,pqModel,i+1)
{
  reveal SumValues;
  DelOne(oldpqModel,m);
  forall e | e in multiset(v[..])
    ensures (e in multiset(w[..i+1]) || e in Values(pqModel))
  {
    if e !in multiset(w[..i+1]) && e !in Values(pqModel) {
      assert e !in multiset(w[..i]);
      assert e in Values(oldpqModel);
      if (e==m.value) {assert false;}
      else {
        assert e in Values(oldpqModel);
        assert Values(oldpqModel-multiset{m})[e] ==  Values(oldpqModel)[e];
        assert false;
      }
    }
  }
  forall e | e in multiset(w[..i+1])
    ensures e in multiset(v[..])
  {
    if e in multiset(w[..i]) {}
    else {
      assert e == w[i] == m.value;
      assert m.value in v[..];
    }
  }
  Restoreaux(oldpqModel,pqModel,m,w,v,i);

}



lemma Restoreaux (oldpqModel:multiset<Solution>, pqModel:multiset<Solution>, m:Solution, w:array<real>, v:array<real>, i:int)
  requires w.Length == v.Length
  requires 0 <= i < w.Length
  requires m in oldpqModel && m.value in Values(oldpqModel) && Values(oldpqModel)[m.value]>0
  requires pqModel == oldpqModel - multiset{m}
  requires m !in pqModel && w[i] == m.value

  requires forall e | e in Values(oldpqModel) && e != m.value ::  Values(oldpqModel-multiset{m})[e] ==  Values(oldpqModel)[e]

  requires m.value in Values(oldpqModel-multiset{m}).Keys ==> Values(oldpqModel-multiset{m})[m.value] ==  Values(oldpqModel)[m.value]-1
  requires if Values(oldpqModel)[m.value]> 1 then Values(pqModel).Keys == Values(oldpqModel).Keys
           else Values(pqModel).Keys == Values(oldpqModel).Keys-{m.value}

  requires forall e | e in multiset(w[..i]) :: e in multiset(v[..])
  requires forall e | e in multiset(v[..]) :: (e in multiset(w[..i+1]) || e in Values(oldpqModel))
  requires forall e | e in multiset(v[..]) ::
             if  e in Values(oldpqModel) && e in multiset(w[..i]) then multiset(v[..])[e] == Values(oldpqModel)[e]  + multiset(w[..i])[e]
             else if e in Values(oldpqModel) && e !in multiset(w[..i]) then  multiset(v[..])[e] == Values(oldpqModel)[e]
             else multiset(v[..])[e] == multiset(w[..i])[e]

  ensures forall e | e in multiset(v[..]) ::
            if  e in Values(pqModel) && e in multiset(w[..i+1]) then multiset(v[..])[e] == Values(pqModel)[e]  + multiset(w[..i+1])[e]
            else if e in Values(pqModel) && e !in multiset(w[..i+1]) then  multiset(v[..])[e] == Values(pqModel)[e]
            else multiset(v[..])[e] == multiset(w[..i+1])[e]
{}



/* Método: inserta los elementos de un vector de entrada v a una cola de prioridad  */
method FillPQ(v : array<real>) returns(pq:PriorityQueue)//41,4s -> 58,2s
  ensures fresh(pq) && fresh(pq.arr)
  ensures pq.Valid() && |pq.Model()| == v.Length == |v[..]|
  ensures SameValues(v, pq, v.Length)
  ensures forall s | s in pq.Model() :: pq.Model()[s] == 1
{
  pq := new PriorityQueue();
  var i := 0;

  // Meter valores en la cola
  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant fresh(pq) && fresh(pq.arr)
    invariant pq.Valid()
    invariant SameValues(v,pq,i)
    invariant |pq.Model()| == i
    invariant forall s | s in pq.Model() :: pq.Model()[s] == 1
  {
    var s := new Solution(v[i]);
    ghost var oldpqModel := pq.Model();

    AddValues(pq.Model(),s);
    assert forall e | e in Values(oldpqModel) && e != s.value ::  Values(oldpqModel+multiset{s})[e] ==  Values(oldpqModel)[e];
    assert s.value !in Values(oldpqModel) ==> Values(oldpqModel+multiset{s})[s.value] == 1;

    pq.Insert(s);
    assert pq.Model() == oldpqModel + multiset{s};
    assert v[..i+1] == v[..i] + [v[i]];
    assert  multiset(v[..i+1]) == multiset(v[..i]) + multiset{v[i]};
    assert v[i] in Values(pq.Model());

    i := i + 1;

  }
  assert v[..i] == v[..];
}


/* Método: extrae los elementos de la cola de prioridad añadiendolos en un vector w */
method {:only} ExtractPQ(v:array<real>,pq:PriorityQueue) returns (w:array<real>)//27,7 s
  modifies pq,pq.arr
  requires  pq.Valid()
  requires |pq.Model()| == v.Length
  requires SameValues(v,pq,v.Length)
  requires forall s | s in pq.Model() :: pq.Model()[s] == 1
  ensures pq.Valid() && pq.IsEmpty() && |pq.Model()| == 0
  ensures fresh(w) && w.Length == v.Length
  ensures multiset(w[..]) == multiset(v[..]) // el nuevo array w es una permutacion de v
{
  w := new real[v.Length];
  assert |pq.Model()| == v.Length == w.Length;
  var i := 0;
  // Extracción ordenada

  //El invariante se cumple al principio
  assert multiset(w[..i]) == multiset{};
  ghost var fullpq := Values(pq.Model());
  assert (v[..v.Length]) == (v[..]);
  assert SumValues(v,w,pq.Model(),0) by {reveal SumValues;}

  while i < w.Length
    decreases w.Length - i
    invariant 0 <= i <= v.Length == w.Length
    invariant pq.Valid()
    invariant forall s | s in pq.Model() :: pq.Model()[s]==1
    invariant |pq.Model()| + i == w.Length
    invariant fresh(w)
    invariant pq.arr == old(pq.arr) || fresh(pq.arr)
    invariant multiset{pq} !! multiset{pq.arr as object} !! multiset{w} !! multiset{v} !! pq.Model()
    invariant Values(pq.Model()).Keys <= fullpq.Keys
    invariant fullpq.Keys == set x <- v[..]

    invariant SumValues(v,w,pq.Model(), i)
  {
    //El invariante se cumple al principio del cuerpo del bucle
    assert SumValues(v,w,pq.Model(),i);
    ghost var oldpqModel := pq.Model();
    assert |oldpqModel| + i == w.Length;
    assert SumValues(v,w,oldpqModel,i);
    ghost var mi:= multiset(w[..i]);

    var m := pq.Min();

    assert SumValues(v,w,oldpqModel,i);

    w[i] := m.value;

    //Aunque w ha cambiado la parte de w[..i] no ha cambiado
    //porque solo ha cambiado la posicion i
    assert pq.Model() == oldpqModel;
    assert w[..i+1] == w[..i] + [w[i]];
    assert multiset(w[..i])==mi;

    pq.DeleteMin();

    //Como w[..i] no ha cambiado SumValues se sigue cumpliendo
    //para oldpqModel, igual que antes
    assert w[..i+1] == w[..i] + [w[i]];
    assert multiset(w[..i])==mi;
    assert SumValues(v,w,oldpqModel,i) by {reveal SumValues;}

    //Restauramos el invariante llamando a Restore
    Restore(oldpqModel,pq.Model(),m,w,v,i);
    assert SumValues(v,w,pq.Model(),i+1);
    assert Values(pq.Model()).Keys <= fullpq.Keys ;
    assert fullpq.Keys == set x <- v[..];

    assert |pq.Model()| == |oldpqModel| - 1;
    assert |pq.Model()| + (i+1) == |oldpqModel| + i == w.Length;


    i := i + 1;
    // assert SumValues(v,w,pq.Model(),i);
    // assert |pq.Model()| + i == w.Length ;
    // assert multiset{pq} !! multiset{pq.arr as object} !! multiset{w} !! pq.Model();
    // assert pq.arr == old(pq.arr) || fresh(pq.arr);


  }
  //Una vez consumida la cola de prioridad, todos los elementos están en w, con la misma
  //multiplicidad que en v
  //Ademas, w está ordenado
  assert |pq.Model()| == 0;

  FinalValues(v,w,pq);
}


method Heapsort(v : array<real>) returns (w : array<real>)
  ensures multiset(w[..]) == multiset(v[..]) // el nuevo array w es una permutacion de v
{
  var pq := FillPQ(v);
  w := ExtractPQ(v,pq);
}

  


