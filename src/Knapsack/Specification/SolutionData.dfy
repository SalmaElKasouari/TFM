/*-----------------------------------------------------------------------------------------------------------------

El tipo SolutionData es el modelo de la representación formal de las soluciones del problema de la mochila. 
Proporciona las herramientas necesarias para verificar diferentes configuraciones de una solución.

Estructura del fichero:

  Datatype
  - itemsAssign: array de bool de tamaño número de objetos donde cada posición corresponde a un objeto y cuyo 
    valor almacenado indica si el objeto ha sido seleccionado (true) o no (false).
  - k: etapa del árbol de exploración de la solución. Denota el número de objetos tratados de itemsAssign. 

  Funciones
    - TotalWeight: suma total de los pesos de los objetos seleccionados.
    - TotalValue: suma total de los valores de los objetos seleccionados.
  
  Predicados
    - Explicit: restricciones explícitas del problema.
    - Implicit: restricciones implícitas del problema.
    - Partial: una solución parcial es válida.
    - Valid: una solución completa es válida.
    - Optimal: una solución es óptima.
    - Extends: una solución extiende de otra.
    - OptimalExtension: una solución es extensión óptima de otra.
    - Equals: una solución es igual a otra (igualdad de campos).

  Lemas
    - SumOfFalsesEqualsZero: si todas las posiciones de itemsAssign están a false, entonces la suma de los 
      pesos/valores es 0.
    - AddTrueMaintainsSumConsistency: 
    - AddFalsePreservesWeightValue:
    - EqualValueWeightFromEquals: dos solciones iguales tienen el mismo peso total y valor total.
    - GreaterOrEqualValueWeightFromExtends: si una solución que extiende a otra, entonces tiene como mínimo el peso 
      y valor totales de la solución original.
    - EqualsOptimalExtensionFromEquals: si dos soluciones son iguales, entonces tienen las mismas extensiones 
      óptimas.

-----------------------------------------------------------------------------------------------------------------------*/

include "InputData.dfy"
include "ItemData.dfy"
include "../Implementation/Input.dfy"

module SolutionData {

  import opened ItemData
  import opened InputData

  datatype SolutionData = SolutionData(itemsAssign: seq<bool>, k: nat) {

    /* Funciones */

    /*
      function: calcula el peso total de los objetos seleccionados hasta el índice k. Si el objeto está seleccionado
      se añade su peso al peso total acumulado de la solución. Si no está seleccionado, se mantiene el peso acumulado 
      sin incluirlo. La function es recursiva y depende de las decisiones tomadas hasta el índice k-1.
    */
    ghost function TotalWeight(items: seq<ItemData>): real
      decreases k
      requires Explicit(items)
    {
      if k == 0 then
        0.0
      else if itemsAssign[k-1] then
        SolutionData(itemsAssign, k - 1).TotalWeight(items) + items[k-1].weight
      else
        SolutionData(itemsAssign, k - 1).TotalWeight(items)
    }


    /*
      function: calcula el valor total de los objetos seleccionados hasta el índice k. Si el objeto está seleccionado
      se añade su valor al valor total acumulado de la solución. Si no está seleccionado, se mantiene el valor 
      acumulado sin incluirlo. La function es recursiva y depende de las decisiones tomadas hasta el índice k-1.
    */
    ghost function TotalValue(items: seq<ItemData>): real
      decreases k
      requires Explicit(items)
    {
      if k == 0 then
        0.0
      else if itemsAssign[k-1] then
        SolutionData(itemsAssign, k - 1).TotalValue(items) + items[k-1].value
      else
        SolutionData(itemsAssign, k - 1).TotalValue(items)
    }


    /* Predicados */

    /*
      Predicado: restricciones explícitas del problema.
    */
    ghost predicate Explicit (items: seq<ItemData>){
      && 0 <= k <= |items| == |itemsAssign|
    }


    /*
      Predicado: restricciones implícitas del problema.
    */
    ghost predicate Implicit(items: seq<ItemData>, maxWeight : real)
      requires Explicit(items)
    {
      TotalWeight(items) <= maxWeight
    }


    /*
      Predicado: verifica que una solución parcial sea válida hasta el índice k, respetando todas las restricciones 
      sdel problema.
    */
    ghost predicate Partial (input: InputData)
      requires input.Valid()
    {
      && Explicit(input.items)
      && Implicit(input.items, input.maxWeight)
    }


    /*
      Predicado: verifica que la solución esté completa (hemos tratado todos los objetos) y sea válida, respetando 
      todas las restricciones del problema.
    */
    ghost predicate Valid(input: InputData)
      requires input.Valid()
    {
      && k == |itemsAssign|
      && Partial(input)
    }


    /*
      Predicado: la prioridad es una cota superior para todas las extensiones válidas de la solución parcial.
    */
    ghost predicate IsUpperBound(priority : real, input : InputData)
      requires input.Valid()
    {
      //forall s : SolutionData | s.Valid(input) && s.OptimalExtension(this, input) :: s.TotalValue(input.items) <= priority
      forall s : SolutionData | s.Valid(input) && s.k <= |itemsAssign| == |s.itemsAssign| && k <= s.k && s.Extends(this) :: s.TotalValue(input.items) <= priority

    }


    /*
      Predicado: asegura que una solución válida (this) sea óptima, es decir, que no exista ninguna otra solución 
      válida con un mayor valor total.
    */
    ghost predicate Optimal(input: InputData)
      requires input.Valid()
      requires Valid(input)
    {
      forall s: SolutionData | s.Valid(input) :: s.TotalValue(input.items) <= TotalValue(input.items)
    }


    /*
      Predicado: verifica una solución es una extensión de la solución parcial (ps), manteniendo la igualdad 
      hasta el índice k.
    */
    ghost predicate Extends(ps : SolutionData) // ps es prefijo de ps' (el que llama a la function), (ps y ps' iguales hasta k)
      requires k <= |itemsAssign| == |ps.itemsAssign|
      requires ps.k <= k
    {
      forall i | 0 <= i < ps.k :: itemsAssign[i] == ps.itemsAssign[i]
    }


    /*
      Predicado: verifica que una solución (this) es una extensión óptima de la solución parcial ps, garantizando que no haya 
      soluciones válidas con un mayor valor total que 
    */
    ghost predicate OptimalExtension(ps : SolutionData, input : InputData)
      requires input.Valid()
    {
      && Valid(input)
      && ps.Partial(input)
      && Extends(ps)
      && forall s : SolutionData | s.Valid(input) && s.Extends(ps) :: s.TotalValue(input.items) <= TotalValue(input.items)
    }


    /*
      Predicado: verifica que dos soluciones this y s sean iguales hasta el índice k, es decir, que cuentan con la 
      misma asignación de objetos seleccionados.
    */
    ghost predicate Equals(s : SolutionData)
      requires |itemsAssign| == |s.itemsAssign|
      requires k <= |itemsAssign|
      requires s.k <= |s.itemsAssign|
    {
      && k == s.k
      && forall i | 0 <= i < k :: itemsAssign[i] == s.itemsAssign[i]
    }

    /*
      Predicado: verifica que una solución tenga a partir de k todos sus elementos a false.
    */
    ghost predicate AllFalsesFromK()
    {
      forall i | k <= i < |itemsAssign| :: itemsAssign[i] == false
    }



    /* Funciones */


    /*
    Función: devuelve el nodo raíz cuyos componentes son false 
    */
    static ghost function rootData(input : InputData) : SolutionData
    {
      SolutionData(seq(|input.items|, i => false), 0)
    }


    /*
    Función: devuelve el conjunto de las soluciones completas (hojas) que son extensiones de this 
    */
    ghost function Extensions() : set<SolutionData>
      decreases |itemsAssign| - k
      requires 0 <= k <= |itemsAssign|
      ensures Extensions() <= PartialExtensions()
    {
      if k == |itemsAssign| then
        {this}
      else
        SolutionData(itemsAssign[k := false], k + 1).Extensions() +
        SolutionData(itemsAssign[k := true], k + 1).Extensions()
    }


    /*
    Función: devuelve el conjunto de las soluciones parciales que son extensiones de this 
    */
    ghost function PartialExtensions() : set<SolutionData>
      decreases |itemsAssign| - k
      requires 0 <= k <= |itemsAssign|
    {
      { this } +
      if k == |itemsAssign| then
        {}
      else
        SolutionData(itemsAssign[k := false], k + 1).PartialExtensions() +
        SolutionData(itemsAssign[k := true],  k + 1).PartialExtensions()
    }



    /* Lemas */

    static lemma InExtensionsExtends(input:InputData, parent:SolutionData, s:SolutionData)
      decreases |input.items| - parent.k
      requires input.Valid()
      requires parent.k <= |parent.itemsAssign|==|input.items|
      requires s in parent.Extensions()
      ensures parent.k <= s.k <= |s.itemsAssign| == |parent.itemsAssign| && s.Extends(parent)
    {      
      assert s in parent.PartialExtensions();
      ItemsAssignSize(input,parent,s);
    }
    

    /*
    Lema: todas las extensiones de una solucion tienen el mismo tamaño de itemsAssign
    //
    Propósito: demostrar el lema DisjointTreesPropertiesTwoChildren.
    //
    Verificación: 
    */
    static lemma ItemsAssignSize(input:InputData, parent:SolutionData, s:SolutionData)
      decreases |input.items| - parent.k
      requires input.Valid()
      requires parent.k <= |parent.itemsAssign|==|input.items|
      requires s in parent.PartialExtensions()
      ensures |s.itemsAssign| == |parent.itemsAssign|
    {
      if (s == parent){}
      else if (parent.k == |parent.itemsAssign|){}
      else {
        assert s in SolutionData(parent.itemsAssign[parent.k := false], parent.k + 1).PartialExtensions() ||
               s in SolutionData(parent.itemsAssign[parent.k := true], parent.k + 1).PartialExtensions();

        if (s in SolutionData(parent.itemsAssign[parent.k := false], parent.k + 1).PartialExtensions()) {
          ItemsAssignSize(input, SolutionData(parent.itemsAssign[parent.k := false], parent.k+1), s);
        }
        else {
          ItemsAssignSize(input, SolutionData(parent.itemsAssign[parent.k := true], parent.k+1), s);
        }
      }
    }


    /*
    Lema: si s extiende a un hijo true o false entonces extiende al padre.
    //
    Propósito: demostrar el lema DisjointTreesPropertiesTwoChildren.
    //
    Verificación: 
    */
    static lemma InPartialExtensions(input:InputData, parent:SolutionData, s:SolutionData)
      decreases |input.items| - parent.k
      requires input.Valid()
      requires parent.k < |parent.itemsAssign| == |input.items|
      requires s in SolutionData(parent.itemsAssign[parent.k := false], parent.k + 1).PartialExtensions() ||
               s in SolutionData(parent.itemsAssign[parent.k := true], parent.k + 1).PartialExtensions()
      ensures  s in parent.PartialExtensions()
      ensures s.k > parent.k
      ensures |s.itemsAssign| == |parent.itemsAssign|
    {
      ItemsAssignSize(input,parent,s);
      if s.k == parent.k+1 {}
      else {
        if s in SolutionData(parent.itemsAssign[parent.k := false], parent.k + 1).PartialExtensions() {
          InPartialExtensions(input,SolutionData(parent.itemsAssign[parent.k := false],parent.k+1),s);
        }
        else {
          InPartialExtensions(input,SolutionData(parent.itemsAssign[parent.k := true],parent.k+1),s);
        }
      }
    }


    /*
    Lema: todas las extensiones con b tienen b en k.
    //
    Propósito: demostrar el lema DisjointTreesPropertiesTwoChildren.
    //
    Verificación: usando los lemas ItemsAssignSize y ItemsAssignEqualUntilK
    */
    static lemma ItemsAssignkth(input:InputData, parent:SolutionData, s:SolutionData, b : bool)
      requires input.Valid()
      requires parent.k < |parent.itemsAssign| == |input.items|
      requires s in parent.PartialExtensions()
      ensures |s.itemsAssign| == |parent.itemsAssign|
      ensures s in SolutionData(parent.itemsAssign[parent.k := b], parent.k + 1).PartialExtensions() ==> s.itemsAssign[parent.k] == b
    {
      ItemsAssignSize(input,parent,s);

      if s == parent { // Demostrar que s no puede ser parent por reducción al absurdo. Si es es parent, entonces parent no puede pertenecer al conjunto de extensiones parciales de de sus hijos.
        if s in SolutionData(parent.itemsAssign[parent.k := b], parent.k+1).PartialExtensions() { // Suponiendo que sí, el lema InPartialExtensions implicaría que parent.k > parent.k + 1, lo cual es imposible.
          InPartialExtensions(input,SolutionData(parent.itemsAssign[parent.k := b], parent.k+1),s);
          assert false;
        }
      }
      else {
        if parent.k + 1 == |parent.itemsAssign| {}
        else {
          if s in SolutionData(parent.itemsAssign[parent.k := b], parent.k+1).PartialExtensions() {
            PartialExtensionsEqualUntilK(input, SolutionData(parent.itemsAssign[parent.k := b], parent.k+1), s);
          }
        }
      }
    }

    /*
    Lema: si s pertenece a las extensiones de parent, entonces tienen itemsAssign igual hasta la posición k.
    //
    Propósito: demostrar el lema ItemsAssignkth.
    //
    Verificación: usando los lemas ItemsAssignSize y ItemsAssignEqualUntilK
    */
    static lemma PartialExtensionsEqualUntilK(input:InputData, parent:SolutionData, s:SolutionData)
      decreases |input.items| - parent.k
      requires input.Valid()
      requires parent.k < |parent.itemsAssign| == |input.items|
      requires s in parent.PartialExtensions()
      ensures |s.itemsAssign| == |parent.itemsAssign|
      ensures s.k >= parent.k
      ensures s.itemsAssign[..parent.k] == parent.itemsAssign[..parent.k]
    {
      ItemsAssignSize(input, parent, s);

      if (s == parent) {}
      else {
        assert s in SolutionData(parent.itemsAssign[parent.k := false], parent.k + 1).PartialExtensions() ||
               s in SolutionData(parent.itemsAssign[parent.k := true], parent.k + 1).PartialExtensions();
      }
    }


    /* 
    Lema: todas las SolutionData válidas extienden a la raiz del arbol y por tanto estan en sus extensiones.
    //
    Propósito: 
    //
    Demostración: usando el lema ExtendsInExtensions.
    */
    lemma AllSolutions(input : InputData, s : SolutionData)
      requires input.Valid()
      requires s.Valid(input)
      ensures s.Extends(rootData(input))
      ensures s in rootData(input).Extensions()
    {
      ExtendsInExtensions(input, s, rootData(input));
    }


    /* 
    Lema: una SolutionData s valida que extiende a otra f parcial ha de estar en el conjunto Extensions de f.
    //
    Propósito: demostrar el lema AllSolutions.
    //
    Demostración: por inducción en f.
    */
    static lemma ExtendsInExtensions(input : InputData, s : SolutionData, f : SolutionData)
      decreases |input.items| - f.k
      requires input.Valid()
      requires s.Valid(input) && f.Partial(input)
      requires s.Extends(f)
      ensures s in f.Extensions()
    {
      if (s.k == f.k) {
        assert s.k == |input.items|;
        assert s.itemsAssign[..] == f.itemsAssign[..];
        assert s == f;
      }
      else {
        var ftrue := SolutionData(f.itemsAssign[f.k := true], f.k + 1);
        var ffalse := SolutionData(f.itemsAssign[f.k := false], f.k + 1);
        assert s.Extends(ftrue) || s.Extends(ffalse);
        if (s.Extends(ftrue)) {
          if (ftrue.Partial(input)) {}
          else { ExtendsNotPartialNotValid(input, s, ftrue);}
        }
        else {
          if (ffalse.Partial(input)) {}
          else { ExtendsNotPartialNotValid(input, s, ffalse);}
        }
      }
    }

    /* 
    Lema: una SolutionData s que extiende a otra f que no es parcial, no puede ser solucion valida.
    //
    Propósito: demostrar el lema ExtendsInExtensions
    //
    Demostración: por inducción en f.
    */
    static lemma ExtendsNotPartialNotValid(input : InputData, s : SolutionData, f : SolutionData)
      decreases |input.items| - f.k
      requires input.Valid()
      requires !f.Partial(input)
      requires f.k <= s.k == |s.itemsAssign| == |f.itemsAssign| == |input.items|
      requires s.Extends(f)
      ensures !s.Valid(input)
    {
      if (f.k == s.k) {
        assert s.itemsAssign[..] == f.itemsAssign[..];
        assert s == f;
      }
      else {
        var ftrue := SolutionData(f.itemsAssign[f.k := true], f.k + 1);
        var ffalse := SolutionData(f.itemsAssign[f.k := false], f.k + 1);
        assert s.Extends(ftrue) || s.Extends(ffalse);
        assert !f.Implicit(input.items, input.maxWeight);

        if (s.Extends(ftrue)) {
          SolutionData.AddTrueMaintainsSumConsistency(f, ftrue, input);
          assert !ftrue.Partial(input);
          ExtendsNotPartialNotValid(input, s, ftrue);
        } else {
          SolutionData.AddFalsePreservesWeightValue(f, ffalse, input);
          assert !ffalse.Partial(input);
          ExtendsNotPartialNotValid(input, s, ffalse);
        }
      }
    }


    /* 
    Lema: Todas las SolutionData parciales extienden a la raiz del arbol y por tanto estan en sus extensiones.
    //
    Propósito: demostrar que todas las soluciones parciales están en PartialPending, el conjunto de soluciones parciales de la cola que no han sido procesadas.
    //
    Demostración: usando el lema ExtendsInPartialExtensions.
    */
    lemma AllNodes(input: InputData, s : SolutionData)
      requires input.Valid()
      requires s.Partial(input)
      requires s.itemsAssign[s.k..] == rootData(input).itemsAssign[s.k..]
      ensures s.Extends(rootData(input))
      ensures s in rootData(input).PartialExtensions()
    {
      ExtendsInPartialExtensions(input, s, rootData(input));
    }


    /* Generalización del lema anterior */
    lemma AllNodesG(input : InputData)
      requires input.Valid()
      ensures forall sd : SolutionData | sd.Partial(input) && sd.AllFalsesFromK() :: sd in rootData(input).PartialExtensions()
    {
      forall sd : SolutionData | sd.Partial(input) && sd.AllFalsesFromK()
        ensures sd in rootData(input).PartialExtensions()
      {
        AllNodes(input, sd);
      }
    }


    /* 
    Lema: una SolutionData s parcial que extiende a otra f parcial ha de estar en el conjunto Extensions de f.
    //
    Propósito: demostrar el lema AllSolutions.
    //
    Demostración: por inducción en f.
    */
    static lemma ExtendsInPartialExtensions(input : InputData, s : SolutionData, f : SolutionData)
      decreases |input.items| - f.k
      requires input.Valid()
      requires f.k <= s.k
      requires s.Partial(input) && f.Partial(input)
      requires s.Extends(f)
      requires s.itemsAssign[s.k..] == f.itemsAssign[s.k..]
      ensures s in f.PartialExtensions()
      ensures s.PartialExtensions() <= f.PartialExtensions()
    {
      if (s.k == f.k) {
        assert s.itemsAssign[..s.k] == f.itemsAssign[..f.k];
        assert s == f;
      }
      else {
        var ftrue := SolutionData(f.itemsAssign[f.k := true], f.k + 1);
        var ffalse := SolutionData(f.itemsAssign[f.k := false], f.k + 1);
        assert s.Extends(ftrue) || s.Extends(ffalse);

        if (s.Extends(ftrue)) {
          if (ftrue.Partial(input)) { }
          else { ExtendsNotPartialNotPartial(input, s, ftrue);}
        }
        else {
          if (ffalse.Partial(input)) { }
          else { ExtendsNotPartialNotPartial(input, s, ffalse);}
        }
      }
    }


    /* 
    Lema: una SolutionData s que extiende a otra f que no es parcial, no puede ser solucion parcial.
    //
    Propósito: demostrar el lema ExtendsInPartialExtensions
    //
    Demostración: por inducción en f.
    */
    static lemma ExtendsNotPartialNotPartial(input : InputData, s : SolutionData, f : SolutionData)
      decreases |input.items| - f.k
      requires input.Valid()
      requires !f.Partial(input)
      requires f.k <= s.k <= |s.itemsAssign| == |f.itemsAssign| == |input.items|
      requires s.Extends(f)
      requires s.itemsAssign[s.k..] == f.itemsAssign[s.k..]
      ensures !s.Partial(input)
    {
      if (f.k == s.k) {
        assert s.itemsAssign[..] == f.itemsAssign[..];
      }
      else {
        var ftrue := SolutionData(f.itemsAssign[f.k := true], f.k + 1);
        var ffalse := SolutionData(f.itemsAssign[f.k := false], f.k + 1);
        assert s.Extends(ftrue) || s.Extends(ffalse);
        assert !f.Implicit(input.items, input.maxWeight);

        if (s.Extends(ftrue)) {
          SolutionData.AddTrueMaintainsSumConsistency(f, ftrue, input);
          assert !ftrue.Partial(input);
          ExtendsNotPartialNotPartial(input, s, ftrue);
        } else {
          SolutionData.AddFalsePreservesWeightValue(f, ffalse, input);
          assert !ffalse.Partial(input);
          ExtendsNotPartialNotPartial(input, s, ffalse);
        }
      }
    }


    /* 
    Lema: dado un itemsAssign cuyas posiciones son todas a false, es decir, que ningun objeto ha 
    sido seleccionado, garantiza que la suma de los pesos y la suma de los valores son nulas.
    //
    Propósito: demostrar que ps es inicialmente Partial en el Method ComputeSolution de Knapsack.dfy
    //
    Demostración: por inducción ya que las definiciones de TotalWeight y Totalvalue son recursivas.
    */
    lemma SumOfFalsesEqualsZero(input : InputData)
      decreases k
      requires input.Valid()
      requires k <= |itemsAssign|
      requires |itemsAssign| == |input.items|
      requires forall i | 0 <= i < |itemsAssign| :: !itemsAssign[i]
      ensures && TotalWeight(input.items) == 0.0
              && TotalValue(input.items) == 0.0
    {}


    /* 
    Lema: dada una solución s1 que se extiende añadiendo un elemento a true generando una nueva 
    solución s2, la suma de los pesos y los valores de s2 se actualiza de manera consistente al incluir el peso y
    el valor del nuevo elemento.
    //
    Propósito: garantizar la consistencia de los datos entre las versiones antigua y actual del modelo de la solución 
    en el lema PartialConsistency de BT.dfy.
    //
    Demostración: mediante el lema EqualValueWeightFromEquals.
    */
    static lemma AddTrueMaintainsSumConsistency(s1 : SolutionData, s2 : SolutionData, input : InputData) //s1 viejo, s2 nuevo
      decreases s1.k
      requires input.Valid()
      requires 0 <= s1.k <= |s1.itemsAssign|
      requires 0 < s2.k <= |s2.itemsAssign|
      requires |s2.itemsAssign| == |s1.itemsAssign| == |input.items|
      requires s2.k == s1.k + 1
      requires s1.itemsAssign[..s1.k] + [true] == s2.itemsAssign[..s2.k]
      ensures s1.TotalWeight(input.items) + input.items[s1.k].weight ==
              s2.TotalWeight(input.items)
      ensures s1.TotalValue(input.items) + input.items[s1.k].value ==
              s2.TotalValue(input.items)
    {
      s1.EqualValueWeightFromEquals(SolutionData(s2.itemsAssign, s2.k-1), input);
    }


    /* 
    Lema: dada una solución s1 que se extiende añadiendo un elemento a false generando una nueva 
    solución s2, la sumas de los pesos y los valores siguen siendo las mismas y no se ven alteradas (ya que no sumaría 
    el peso/valor del objeto como se ve en la definición de Totalweight y TotalValue).
    //
    Propósito: demostrar que ps sigue siendo Partial después de asignar el objeto k a false en KnapsackBTFalseBranch 
    de BT.dfy.
    //
    Demostración: mediante el lema EqualValueWeightFromEquals.
    */
    static lemma AddFalsePreservesWeightValue(s1 : SolutionData, s2 : SolutionData, input : InputData) //s1 viejo, s2 nuevo
      decreases s1.k
      requires input.Valid()
      requires 0 <= s1.k <= |s1.itemsAssign|
      requires 0 < s2.k <= |s2.itemsAssign|
      requires |s2.itemsAssign| == |s1.itemsAssign| == |input.items|
      requires s2.k == s1.k + 1
      requires s1.itemsAssign[..s1.k] + [false] == s2.itemsAssign[..s2.k]
      ensures s1.TotalWeight(input.items) == s2.TotalWeight(input.items)
      ensures s1.TotalValue(input.items) == s2.TotalValue(input.items)
    {
      s1.EqualValueWeightFromEquals(SolutionData(s2.itemsAssign, s2.k-1), input);
    }


    /* 
    Lema: si dos soluciones (this y s) son idénticas (igualdad de campos), entonces tienen las mismas 
    sumas de pesos y valores. Esto es por que el contenido de itemsAssign de cada solución es igual y los cálculos 
    acumulativos de pesos y valores serán idénticos.
    //
    Propósito: demostrar el lema AddTrueMaintainsSumConsistency y el lema EqualsOptimalExtensionFromEquals.
    //
    Demostración: mediante inducción en this y s.
    */
    lemma EqualValueWeightFromEquals(s : SolutionData, input : InputData)
      decreases k
      requires input.Valid()
      requires |input.items| == |itemsAssign| == |s.itemsAssign|
      requires k <= |itemsAssign|
      requires s.k <= |s.itemsAssign|
      requires Equals(s)
      ensures TotalValue(input.items) == s.TotalValue(input.items)
      ensures TotalWeight(input.items) == s.TotalWeight(input.items)
    {
      if k == 0 {

      }
      else {
        SolutionData(itemsAssign, k - 1).EqualValueWeightFromEquals(SolutionData(s.itemsAssign, s.k - 1), input);
      }
    }


    /* 
    Lema: sea una solución s que extiende a this, entonces el peso total y valor total de s deben ser al menos 
    iguales al peso total y valor total de ps. Esto es por que el contenido de employeesAssign de cada solución es 
    igual hasta k.
    //
    Propósito: demostrar el lema InvalidExtensionsFromInvalidPs de BT.dfy.
    //
    Demostración: mediante inducción en s, esta se va reduciendo hasta k.
    */
    lemma GreaterOrEqualValueWeightFromExtends(s: SolutionData, input: InputData)
      decreases s.k
      requires input.Valid()
      requires |itemsAssign| == |s.itemsAssign| == |input.items|
      requires k <= |itemsAssign|
      requires s.k <= |s.itemsAssign|
      requires k <= s.k
      requires s.Extends(this)
      ensures s.TotalWeight(input.items) >= TotalWeight(input.items)
      ensures s.TotalValue(input.items) >= TotalValue(input.items)
    {
      if k == s.k {
        EqualValueWeightFromEquals(s, input);
      }
      else {
        ghost var s := SolutionData(s.itemsAssign, s.k-1);
        GreaterOrEqualValueWeightFromExtends(s, input);
      }
    }


    /* 
    Lema: dadas dos soluciones parciales ps1 y ps2 que son idénticas (igualdad de campos) y 
    sabiendo que bs es una extension óptima de ps1, entonces bs también es extensión optima de ps2.
    //
    Propósito: verificar que bs es la extensión óptima de ps al salir de la rama true en KnapsackBT de BT.dfy.
    //
    Demostración: mediante el lema EqualValueWeightFromEquals.
    */
    lemma EqualsOptimalExtensionFromEquals(ps1 : SolutionData, ps2: SolutionData, input : InputData)
      requires input.Valid()
      requires Valid(input)
      requires |ps1.itemsAssign| == |ps2.itemsAssign|
      requires ps1.k <= |ps1.itemsAssign|
      requires ps2.k <= |ps2.itemsAssign|
      requires ps1.Equals(ps2)
      requires OptimalExtension(ps1, input)
      ensures OptimalExtension(ps2, input)
    {

      assert ps1.k == ps2.k && forall i | 0 <= i < ps1.k :: ps1.itemsAssign[i] == ps2.itemsAssign[i]; //def clave de Equals

      assert OptimalExtension(ps2, input) by {
        assert ps2.Partial(input) by {
          assert ps2.TotalWeight(input.items) <= input.maxWeight by {
            ps1.EqualValueWeightFromEquals(ps2, input);
          }
        }
        assert Extends(ps2);
        assert forall s : SolutionData | s.Valid(input) && s.Extends(ps2) :: s.TotalValue(input.items) <= TotalValue(input.items);
      }
    }


    /* 
    Lema: dada una solución parcial ps y otra solución ps' que extiende a ella con todos las asignaciones a true, 
    entonces ps' siempre es bound superior de cualquier otra extensión de ps.
    //
    Propósito: verificar el Method Bound en BTBound.dfy.
    //
    Demostración: usando los lemas EqualValueWeightFromEquals y AllTruesIsUpperBound.
    */
    static lemma AllTruesIsUpperBoundForAll(ps : SolutionData, ps' : SolutionData, input : InputData)
      requires ps.k <= ps'.k == |ps'.itemsAssign| == |ps.itemsAssign| == |input.items|
      requires input.Valid()
      requires ps'.Extends(ps)
      requires forall j | ps.k <= j < |ps'.itemsAssign| :: ps'.itemsAssign[j]
      ensures forall s : SolutionData | |s.itemsAssign| == |ps.itemsAssign|
                                        && s.k == |s.itemsAssign|
                                        && ps.k <= s.k
                                        && s.Extends(ps) ::
                s.TotalValue(input.items) <= ps'.TotalValue(input.items)
    {
      forall s : SolutionData | && |s.itemsAssign| == |ps.itemsAssign|
                                && s.k == |s.itemsAssign|
                                && ps.k <= s.k
                                && s.Extends(ps)
        ensures s.TotalValue(input.items) <= ps'.TotalValue(input.items)
      {
        assert SolutionData(s.itemsAssign, ps.k).Equals(ps);
        assert SolutionData(ps'.itemsAssign, ps.k).Equals(ps);
        SolutionData(s.itemsAssign, ps.k).EqualValueWeightFromEquals(SolutionData(ps'.itemsAssign, ps.k), input);
        SolutionData.AllTruesIsUpperBound(ps.k, s, ps, ps', input);
      }
    }


    /*
    Lema: dada una solución parcial ps, una solución completa ps' que extiende a ella con todos las asignaciones a 
    true, y otra solución completa s que extiende a ps, entonces ps' es cota superior a s.
    //
    Propósito: demostrar el lema AllTruesIsUpperBoundForAll.
    //
    Demostración: mediante inducción en i.
    */
    static lemma AllTruesIsUpperBound(i : int, s : SolutionData, ps : SolutionData, ps' : SolutionData, input :InputData)
      decreases |ps.itemsAssign| - i
      requires input.Valid()
      requires ps.k <= ps'.k == |input.items| == |ps'.itemsAssign| == |ps.itemsAssign| == |s.itemsAssign|
      requires ps.k <= i <= |ps.itemsAssign|
      requires forall j | ps.k <= j < |ps'.itemsAssign| :: ps'.itemsAssign[j]
      requires && s.k == |s.itemsAssign|
               && ps.k <= s.k
      requires ps'.Extends(ps)
      requires s.Extends(ps)
      requires SolutionData(s.itemsAssign, i).TotalValue(input.items)
            <= SolutionData(ps'.itemsAssign, i).TotalValue(input.items)
      ensures s.TotalValue(input.items) <= ps'.TotalValue(input.items)
    {
      if i == |ps'.itemsAssign| {
        assert SolutionData(s.itemsAssign, i) == s;
        assert SolutionData(ps'.itemsAssign, i) == ps';
      }
      else {
        if (s.itemsAssign[i] && ps'.itemsAssign[i]) {
          AllTruesIsUpperBound(i + 1, s, ps, ps', input);
        }
        else {
          AddFalsePreservesWeightValue(SolutionData(s.itemsAssign, i), SolutionData(s.itemsAssign, i+1), input);
          AllTruesIsUpperBound(i + 1, s, ps, ps', input);
        }
      }
    }
  }
}