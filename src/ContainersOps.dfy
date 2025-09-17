/*
 * Función: dado una matriz de tipo T (array2<T>) y un número de filas k, devuelve una secuencia de k secuencias de 
 * tipo T (seq<seq<T>>).
 */
function Array2ToSeqSeq<T>(a : array2<T>, k : int) : seq<seq<T>>
    reads a
    requires 0 <= k <= a.Length0
    ensures k == |Array2ToSeqSeq(a,k)|
    ensures forall i | 0 <= i < k :: a.Length1 == |Array2ToSeqSeq(a,k)[i]|
    ensures forall i,j | 0 <= i < k && 0 <= j < a.Length1 :: Array2ToSeqSeq(a,k)[i][j] == a[i, j]
  {
    if k == 0 then
      []
    else
      Array2ToSeqSeq(a, k-1) + [Array2ToSeq(a, k-1, a.Length1)]
  }

/*
 * Función: dado una matriz de tipo T (array2<T>), una fila k-esima y un numero de columnas j, transforma la fila k
 * del array2 en una secuencia de j elementos de tipo T (seq<T>).
 */
  function Array2ToSeq<T>(a : array2<T>, k : int, j : int) : seq<T>
    reads a
    requires 0 <= k < a.Length0
    requires 0 <= j <= a.Length1
    ensures j == |Array2ToSeq(a,k,j)|
    ensures forall i | 0 <= i < j :: Array2ToSeq(a,k,j)[i] == a[k, i]
  {
    if j == 0 then
      []
    else
      Array2ToSeq(a, k, j-1) + [a[k, j-1]]
  }