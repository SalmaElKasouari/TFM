/*---------------------------------------------------------------------------------------------------------------------

La clase Item implementa una representación formal de los objetos del problema de la mochila. Cada Item cuenta con 
dos atributos: peso y valor.

Estructura del fichero:

  Atributos y constructor

  Predicados
    - Valid: un item es válido.

  Funciones
    - Model: devuelve el modelo de un Item.
    - ValuePerWeight: devuelve el valor por unidad de peso.

---------------------------------------------------------------------------------------------------------------------*/


include "../Specification/ItemData.dfy"

class Item {

  /* Atributos y constructor */
  const weight: real
  const value:  real

  constructor(w: real, v: real)
    ensures this.weight == w
    ensures this.value == v
  {
    this.weight := w;
    this.value := v;
  }


  /* Predicados */

  /*
  Predicado: verifica si un Item es válido.
  */
  ghost predicate Valid()
    reads this
  {
    this.weight > 0.0 && this.value > 0.0
  }


  /* Funciones */

  /*
  Función: devuelve un ItemData, el modelo de un Item.
  */
  ghost function Model() : ItemData
    reads this
  {
    ItemData(this.weight, this.value)
  }


  /*
  Función: devuelve el valor por unidad de peso.
  */
  ghost function ValuePerWeight() : real
    reads this
    requires this.Valid()
  {
    this.value/this.weight
  }

}