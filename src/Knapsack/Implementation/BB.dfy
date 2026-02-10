/* ---------------------------------------------------------------------------------------------------------------------

Este fichero cuenta con la implementación del problema de la mochila (knapsack problem) utilizando el método algorítmico 
de vuelta atrás. Se implementa de manera que el árbol de exploración es un árbol binario, donde las etapas son 
los objetos que se deben tratar, mientras que las ramas del árbol representan las decisiones sobre si incluir o 
no un objeto en la solución.

Estructura del fichero:
  Métodos
    - KnapsackBT: Punto de partida para ejecutar el método algorítmico BT.
    - KnapsackBTBaseCase: Define la condición de terminación.
    - KnapsackBTFalseBranch: Considera no incluir un elemento en la mochila.
    - KnapsackBTTrueBranch: Considera incluir un elemento en la mochila.

  Lemas
    - PartialConsistency: si el peso de una solución oldps mas el peso de un objeto no excede el peso maximo (es 
      Partial), entonces una solución ps que extiende a oldps con ese objeto asignado a true también será Partial.
    - InvalidExtensionsFromInvalidPs: si una solución parcial ps extendida con true no es válida, entonces ninguna 
      de sus extensiones tampoco será válida. 

---------------------------------------------------------------------------------------------------------------------*/


include "PQ.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"

/* Métodos */

/* 
Método: punto de partida del método algorítmico BT. El método explora todas las posibles asignaciones de objetos, 
respetando las restricciones de peso maxWeight) y seleccionando las combinaciones que maximicen el valor total.
Tenemos ps (partial solution) y bs (best solution) de entrada y salida:
  - ps es la solución parcial que se va llenando durante el proceso de vuelta atrás.
  - bs mantiene la mejor solución encontrada hasta el momento
En este contexto, se inicializa bs con todo a false, ya que es un problema de maximización (se busca el valor
más alto). El árbol de búsqueda es un árbol binario que cuenta con dos ramas:
  - Rama True: el objeto es seleccionado pero solo si el peso total no excede el peso máximo permitido.
  - Rama False: el objeto no es seleccionado.
//
Verfificación:
  - En caso de no ejecutar la rama true porque el ítem no cabe en la mochila,
se invoca el lema InvalidExtensionsFromInvalidPs(ps, input).
  - Antes de las llamadas recursivas a las ramas (KnapsackBTTrueBranch y KnapsackBTFalseBranch), se capturan ciertos
    estados y se asegura que las soluciones parciales y óptimas sigan siendo consistentes.
  - Después de la ejecución de las ramas, se valida que la solución parcial se restaure correctamente, garantizando 
    que los valores de peso y valor coincidan con el estado previo a la llamada. Además, en este punto se presentan 
    tres posibles escenarios
*/
method KnapsackBT(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),1 // Función de bound
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  ensures ps.Partial(input)
  ensures ps.Model().Equals(old(ps.Model()))
  ensures ps.k == old(ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

{

  if (ps.k == input.items.Length) { // hemos tratado todos los objetos
    KnapsackBTBaseCase(input, ps, bs);
  }
  else {
    if (ps.totalWeight + input.items[ps.k].weight <= input.maxWeight) {
      KnapsackBTTrueBranch(input, ps, bs);
    }
    else {
      InvalidExtensionsFromInvalidPs(ps, input);
    }

    label L: // capturamos el momento antes de la llamada

    ghost var oldbs := bs.Model();
    assert ps.Model().Equals(old(ps.Model()));
    assert oldbs.OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1), input.Model())
           || oldbs.Equals(old(bs.Model()));


    KnapsackBTFalseBranch(input, ps, bs);

    assert bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k:=false], ps.k+1), input.Model())
           || bs.Model().Equals(oldbs);
    assert ps.Model().Equals(old(ps.Model()));

    /* La extensión óptima (bs) sale de la rama false */
    if bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k := false], ps.k+1), input.Model()) {
      assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
          s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
    }
    /* La extensión óptima (bs) no ha mejorado en ninguna de las ramas y por lo tanto sigue siendo la antigua */
    else if oldbs.Equals(old(bs.Model())) {
      assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
          s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
    }
    /* La extensión óptima (bs) sale de la rama true */
    else {
      /* En este caso la bs es extensión óptima de la rama true, es decir, que la bs que entró en KnapsackFalseBranch 
      (rama false) no ha mejorado y entonces no ha sido modificada, luego es igual a la que entró que es la que sale
      de la rama true.
      */
      assert bs.Model().Equals(oldbs);

      assert old@L(ps.Model()).Equals(ps.Model());
      assert old@L(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1)).Equals(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1));
      assert old(ps.totalWeight + input.items[ps.k].weight <= input.maxWeight);
      bs.Model().EqualsOptimalExtensionFromEquals(old@L(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1)), SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1), input.Model());
      assert oldbs.OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1), input.Model());

      assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
          s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
    }
  }
}

/* 
Método: Caso base del método algorítmico BT (cuando ya se han tratado todos los objetos). Comparte todas las precondiciones 
y postcondiciones que KnapsackBT pero incluye la precondicion de que la etapa del arbol de exploración (k) es igual
que número de objetos de la entrada.
//
Verificación:
 - Caso ps.totalValue > bs.totalValue: se usa el lema EqualValueWeightFromEquals para asegurar que 
  el valor de cualquier solución que sea extensión de ps es igual al valor de ps. Esto asegura que por tanto no hay
  otra solución con un valor mejor, y con el lema CopyModel se confirma que bs se actualizó correctamente y por
  tanto guarda la solución optima.
 - Caso ps.totalValue <= bs.totalValue: se usa el lema EqualValueWeightFromEquals para asegurar que 
  el valor de cualquier solución que sea extensión de ps es igual al valor de ps y como esta es menor o igual que 
  el valor de bs, se asegura que bs sigue almacenando la solución óptima.
*/
method KnapsackBTBaseCase(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound() // Función de bound
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  requires ps.k == input.items.Length

  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().Equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))
{
  /* Hemos encontrado una solución mejor */
  if (ps.totalValue > bs.totalValue) {
    bs.Copy(ps);
    forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model())
      ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) 
    {
      assert s.Equals(ps.Model());
      calc {
        s.TotalValue(input.Model().items);
        {s.EqualValueWeightFromEquals(ps.Model(), input.Model());}
        ps.Model().TotalValue(input.Model().items);
        {bs.CopyModel(ps, input);}
        bs.Model().TotalValue(input.Model().items);
      }
    }
  }
  /* No hemos encontrado una solución mejor */
  else { // ps.totalValue <= bs.totalValue
    forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model())
      ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) 
    {
      assert s.Equals(ps.Model());
      s.EqualValueWeightFromEquals(ps.Model(), input.Model());
      assert s.TotalValue(input.Model().items) == ps.Model().TotalValue(input.Model().items);
    }
  }
}


/* 
Método: rama false del método algorítmico BT. Es un método que trata la rama de NO coger el objeto. Comparte todas 
las precondiciones y postcondiciones que KnapsackBT pero incluye la precondicion de que la etapa del arbol de 
exploración (k) es menor que número de objetos de la entrada.
  - Se asigna la posición actual (ps.k) a false en ps.itemsAssign, lo que significa que el objeto no se selecciona.  
  - Se avanza a la siguiente posición (ps.k := ps.k + 1) y se invoca recursivamente al método KnapsackBT para 
    continuar con la exploración. 
  - Una vez finalizada la recursión, se restaura ps.k a su valor original (ps.k := ps.k - 1) para volver al estado
    previo.
//
Verificación:
  - Se emplea la etiqueta L para capturar el estado de ps justo antes de la llamada recursiva (marcado como 
  old@L), y luego se compara con el estado de la solución al finalizar la recursión, una vez que sus valores han 
  sido restaurados. Esto permite validar que el estado de la solución parcial se restaura correctamente después 
  del retroceso.
*/
method KnapsackBTFalseBranch(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),0 // Función de bound
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  requires ps.k < input.items.Length

  ensures ps.Partial(input)
  ensures ps.Model().Equals(old(ps.Model()))
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=false],ps.k+1), input.Model())
          || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=false],ps.k+1)) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

{
  ghost var oldps := ps.Model();
  ps.itemsAssign[ps.k] := false;
  ps.k := ps.k + 1;

  assert ps.Partial(input) by {
    SolutionData.AddFalsePreservesWeightValue(oldps, ps.Model(), input.Model());
    input.InputDataItems(ps.k-1);
  }

  KnapsackBT(input, ps, bs);

  label L:

  ps.k := ps.k - 1;

  assert SolutionData(ps.Model().itemsAssign[ps.k := false], ps.k + 1) == old@L(ps.Model());

  //La mejor solución deber ser una extension optima de ps
  assert bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k:=false], ps.k+1), input.Model())
         || bs.Model().Equals(old(bs.Model()));

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=false],ps.k+1)) ::
      s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
}

/* 
Método: rama true del método algorítmico BT. Es un método que trata la rama de SI coger el objeto. Comparte todas 
las precondiciones y postcondiciones que KnapsackBT pero incluye la precondicion de que la etapa del arbol de 
exploración (k) es menor que número de objetos de la entrada.
  - Se asigna la posición actual (ps.k) a true en ps.itemsAssign, lo que significa que el objeto se selecciona.  
  - Se actualizan el peso y el valor total de la solución parcial (ps).
  - Se avanza a la siguiente posición (ps.k := ps.k + 1) y se invoca recursivamente al método KnapsackBT para 
    continuar con la exploración. 
// 
Verificación:
  - Se usa el lema PartialConsistency para probar que ps sigue siendo una solución parcial válida según las
    restricciones del problema.
  - Una vez finalizada la exploración, se restauran los valores originales.
  - Se emplea la etiqueta L para capturar el estado de ps justo antes de la llamada recursiva (marcado como 
    old@L), y luego se compara con el estado de la solución al finalizar la recursión, una vez que sus valores han 
    sido restaurados. Esto permite validar que el estado de la solución parcial se restaura correctamente después 
    del retroceso.
*/
method KnapsackBTTrueBranch(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),0 // Función de bound
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  requires ps.k < input.items.Length
  requires ps.totalWeight + input.items[ps.k].weight <= input.maxWeight

  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().Equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  ensures bs.Model().OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1), input.Model())
          || bs.Model().Equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1)) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

{
  assert ps.totalWeight + input.items[ps.k].weight <= input.maxWeight;
  ghost var oldps := ps.Model();
  ghost var oldtotalWeight := ps.totalWeight;
  ghost var oldtotalValue := ps.totalValue;

  ps.itemsAssign[ps.k] := true;
  ps.totalWeight := ps.totalWeight + input.items[ps.k].weight;
  ps.totalValue := ps.totalValue + input.items[ps.k].value;
  ps.k := ps.k + 1;

  PartialConsistency(ps, oldps, input, oldtotalWeight, oldtotalValue);

  KnapsackBT(input, ps, bs);

  label L:

  ps.k := ps.k - 1;
  ps.totalWeight := ps.totalWeight - input.items[ps.k].weight;
  ps.totalValue := ps.totalValue - input.items[ps.k].value;

  assert SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k + 1) == old@L(ps.Model());

  //La mejor solución deber ser una extension optima de ps
  assert bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k + 1), input.Model())
         || bs.Model().Equals(old(bs.Model()));

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k + 1)) ::
      s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
}



/* Lemas */

/*
Lema: si extendemos una solución parcial (oldps) añadiendo un elemento asignado como (true) 
dando lugar a una nueva solución parcial (ps), entonces ps también cumple con las propiedades de consistencia 
parcial definidas por el método Partial. 
//
Propósito: garantizar que ps sigue siendo Partial en KnapsackBTTrueBranch después de añadirle un objeto cuyo peso 
no hacía exceder el peso maximo.
//
Verificación: se realizan cálculos formales para demostrar que el valor y peso de ps son consistentes con oldps:
  - Primer calc: Se usa el lema AddTrueMaintainsSumConsistency para garantizar que el peso total de ps es la suma 
    del peso de oldps mas el nuevo Item. Se usa el lema InputDataItems para garantizar que el peso total de ps es la suma 
    del peso de oldps mas el nuevo ItemData. Finalmente se garantiza que el peso total es menor que el peso máximo.
  - Segundo calc: se parte de ps.totalWeight y se reescribe como la suma de oldtotalWeight y el nuevo Item. Se 
    asegura que oldtotalWeight es igual a oldps.TotalWeight(input.Model().items). Y se usan los lemas InputDataItems 
    y AddTrueMaintainsSumConsistency para demostrar que la transición de oldps a ps es válida. Se asegura que la 
    suma se puede reescribir como ps.Model().TotalWeight(input.Model().items).
  - Tercer calc: análogo al anterior pero aplicado al valor total en lugar del peso.
*/
lemma PartialConsistency(ps: Solution, oldps: SolutionData, input: Input, oldtotalWeight: real, oldtotalValue: real)
  requires input.Valid()
  requires 1 <= ps.k <= ps.itemsAssign.Length
  requires 0 <= oldps.k <= |oldps.itemsAssign|
  requires ps.k == oldps.k + 1
  requires ps.itemsAssign.Length == |oldps.itemsAssign| == input.items.Length
  requires oldps.itemsAssign[..oldps.k] + [true] == ps.itemsAssign[..ps.k]
  requires oldps.Partial(input.Model())
  requires oldtotalWeight == oldps.TotalWeight(input.Model().items)
  requires oldtotalValue == oldps.TotalValue(input.Model().items)
  requires oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight <= input.maxWeight
  requires oldtotalWeight == ps.totalWeight - input.items[oldps.k].weight
  requires oldtotalValue == ps.totalValue - input.items[oldps.k].value
  ensures ps.Partial(input)
{
  assert oldps.Partial(input.Model());
  assert oldtotalWeight == oldps.TotalWeight(input.Model().items);
  assert oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight <= input.maxWeight;

  calc {
     ps.Model().TotalWeight(input.Model().items);
    { SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model()); }
     oldps.TotalWeight(input.Model().items) + input.Model().items[ps.k - 1].weight;
    { input.InputDataItems(ps.k - 1); }
     oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
    <= input.maxWeight;
  }

  calc {
    ps.totalWeight;
    oldtotalWeight + input.items[ps.k - 1].weight;
    oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
    { input.InputDataItems(ps.k - 1);
      SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model());
    }
    ps.Model().TotalWeight(input.Model().items);
  }

  calc {
    ps.totalValue;
    oldtotalValue + input.items[ps.k - 1].value;
    oldps.TotalValue(input.Model().items) + input.items[ps.k - 1].value;
    { input.InputDataItems(ps.k - 1);
      SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model());
    }
    ps.Model().TotalValue(input.Model().items);
  }

  assert ps.Partial(input);
}

/*
Lema: si una solución parcial ps extendida con true no es válida, entonces ninguna de sus extensiones tampoco 
será válida. 
//
Propósito: garantizar en KnapsackBT que en el caso de que no se ejecute la rama true es porque no se han encontrado
soluciones válidas. Por lo tanto, ninguna solución óptima que salga de dicha rama puede ser mejor que bs.
Se aplica después de haber ejecutado KnapsackBTFalseBranch (rama false) en los siguientes 
casos:
  - La bs (extensión óptima de ps) se ha encontrado en dicha rama.
  - La bs (extensión óptima de ps) no se ha encontrado en dicha rama, y por lo tanto es igual a la antigua, (la que 
    salió de la rama true).
//
Verificación: se aplican los lemas GreaterOrEqualValueWeightFromExtends y AddTrueMaintainsSumConsistency para demostrar 
que cualquier solución s extendida tiene como mínimo el peso de la solución original (ps), que ya excedía del peso 
máximo. Como consecuencia, s también incumple esa restricción, y por tanto no será válida.
*/
lemma InvalidExtensionsFromInvalidPs(ps: Solution, input: Input)
  requires input.Valid()
  requires 0 <= ps.k < ps.itemsAssign.Length
  requires ps.itemsAssign.Length == input.items.Length
  requires ps.totalWeight + input.items[ps.k].weight > input.maxWeight
  requires ps.Partial(input)
  ensures forall s : SolutionData | && |s.itemsAssign| == |(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1)).itemsAssign|
                                    && s.k <= |s.itemsAssign| 
                                    && ps.k + 1 <= s.k 
                                    && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1)) 
                                    :: !s.Valid(input.Model())
{

  forall s : SolutionData |
    && |s.itemsAssign| == |SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1).itemsAssign|
    && s.k <= |s.itemsAssign|
    && ps.k + 1 <= s.k
    && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1))
    ensures !s.Valid(input.Model())
  {
    assert s.TotalWeight(input.Model().items) > input.maxWeight by {
      SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1).GreaterOrEqualValueWeightFromExtends(s, input.Model());
      SolutionData.AddTrueMaintainsSumConsistency(ps.Model(), SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1), input.Model());
    }
  }
}