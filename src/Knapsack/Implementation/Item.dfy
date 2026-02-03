/*---------------------------------------------------------------------------------------------------------------------

La clase Item implementa una representación formal de los objetos del problema de la mochila. Cada Item cuenta con 
dos atributos: peso y valor.

Estructura del fichero:

  Atributos y constructor

  Predicates
    - Valid: un item es válido.

  Functions
    - Model: devuelve el modelo de un Item.
    - ValuePerWeight: devuelve el valor por unidad de peso.

---------------------------------------------------------------------------------------------------------------------*/


include "../Specification/ItemData.dfy"

module Item {
  
  import opened ItemData

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


    /* Predicates */

    /*
    Predicate: verifica si un Item es válido.
    */
    ghost predicate Valid()
      reads this
    {
      this.weight > 0.0 && this.value > 0.0
    }


    /* Functions */

    /*
    Function: devuelve un ItemData, el modelo de un Item.
    */
    ghost function Model() : ItemData
      reads this
    {
      ItemData(this.weight, this.value)
    }


    /*
    Function: devuelve el valor por unidad de peso.
    */
    ghost function ValuePerWeight() : real
      reads this
      requires this.Valid()
    {
      this.value/this.weight
    }

  }
}