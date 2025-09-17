/*---------------------------------------------------------------------------------------------------------------------

La clase Input implementa una representación formal de la entrada del problema de la mochila.

Estructura del fichero:

  Atributos y constructor
    - items: lista de objetos.
    - maxWeight: peso máximo de la mochila.

  Predicados
    - Valid: una entrada es válida.
    - SortedItems: el array items esta ordenado de manera decreciente según valor por unidad de peso.

  Funciones
    - ModelAt: devuelve el modelo del objeto en la posición i del array items.
    - ItemsUntil: devuelve una secuencia con los k primeros elementos (Item) del array items convertidos a ItemData.
    - Model: devuelve el modelo de un Input.
  
  Lemas
    - InputDataItems: el peso y valor de un cierto k en items coinciden con el peso y el valor correspondientes
      en el modelo de items.
    - InputDataItemsForAll: generalización del lema anterior.

---------------------------------------------------------------------------------------------------------------------*/


include "Item.dfy"
include "../Specification/InputData.dfy"

class Input {

  /* Atributos y constructor */
  var items: array<Item>
  var maxWeight: real

  constructor(items: array<Item>, maxWeight: real)
    ensures this.items == items
    ensures this.maxWeight == maxWeight
  {
    this.items := items;
    this.maxWeight := maxWeight;
  }



  /* Predicados */

  /* 
  Predicado: verifica que una entrada sea válida, es decir, que su modelo sea válido.
  */
  ghost predicate Valid()
    reads this, items, set i | 0 <= i < items.Length :: items[i]
  {
    this.Model().Valid()
  }


  /* 
  Predicado: verifica que el array items esta ordenado de manera decreciente según valor por unidad de peso.
  */
  ghost predicate SortedItems()
    reads this, items, set i | 0 <= i < items.Length :: items[i]
    requires this.Valid()
  {
    forall i: nat, j: nat | 0 <= i < j < this.items.Length :: this.items[i].ValuePerWeight() > this.items[j].ValuePerWeight()
  }



  /* Funciones */

  /* 
  Función: devuelve el modelo del objeto en la posición i del array items.
  */
  ghost function ModelAt (i : nat) : ItemData
    reads this, items, items[i]
    requires i < items.Length
  {
    items[i].Model()
  }


  /* 
  Función: devuelve una secuencia con los k primeros elementos del array items convertidos a ItemData.
  */
  ghost function ItemsUntil(k: nat): seq<ItemData>
    reads this, items, set i | 0 <= i < k :: items[i]
    requires k <= items.Length
    ensures |ItemsUntil(k)| == k
    ensures forall i | 0 <= i < k :: ItemsUntil(k)[i].weight == this.items[i].weight
    ensures forall i | 0 <= i < k :: ItemsUntil(k)[i].value == this.items[i].value
  {
    if k == 0 then
      []
    else
      ItemsUntil(k-1) + [items[k-1].Model()]
  }


  /* 
  Función: devuelve el modelo de un Input (entrada del problema).
  */
  ghost function Model() : InputData
    reads this, items, set i | 0 <= i < items.Length :: items[i]
    ensures |Model().items| == items.Length
    ensures forall i | 0 <= i < items.Length :: Model().items[i].weight == items[i].weight
    ensures forall i | 0 <= i < items.Length :: Model().items[i].value == items[i].value
  {
    InputData(ItemsUntil(items.Length), maxWeight)
  }



  /* Lemas */

  /*
  Lema: dada una posición k, el peso y el valor del objeto Item en dicha posición del array items, son iguales al
  peso y el valor correspondientes en el modelo de items. 
  //
  Propósito: demostrar el lema PartialConsistency en BT.dfy para asegurar que una solución sigue siendo parcial. 
  Demostrar el lema InputDataItemsForAll.
  //
  Demostración: trivial.
  */
  lemma InputDataItems(k : int)
    requires 0 <= k < items.Length
    ensures items[k].weight == Model().items[k].weight
    ensures items[k].value == Model().items[k].value
  {
    assert Model().items[k].weight == items[k].weight;
    assert Model().items[k].value == items[k].value;
  }

  /*
  Lema: generalización del lema anterior. Establece que para cada item en items, el peso y el valor de ese 
  item coinciden con el peso y el valor correspondientes en el modelo.
  //
  Propósito:
  //
  Demostración: usando el lema InputDataItems.
  */
  lemma InputDataItemsForAll()
    ensures forall k | 0 <= k < items.Length ::
              items[k].weight == Model().items[k].weight &&
              items[k].value == Model().items[k].value
  {
    var n := items.Length;

    if n == 0 {
      assert forall k | 0 <= k < items.Length ::
          items[k].weight == Model().items[k].weight &&
          items[k].value == Model().items[k].value;
    }
    else {
      forall k | 0 <= k < items.Length
        ensures items[k].weight == Model().items[k].weight &&
                items[k].value == Model().items[k].value
      {
        InputDataItems(k);
      }
    }
  }
}
