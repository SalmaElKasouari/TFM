/*-----------------------------------------------------------------------------------------------------------------

El tipo ItemData es el modelo de la representación formal de los objetos del problema de la mochila.

Estructura del fichero:

  Datatype
  - weight: peso del objeto.
  - value: valor del objeto.
  
  Predicados
    - Valid: un objeto es válido.

-----------------------------------------------------------------------------------------------------------------------*/

datatype ItemData = ItemData(weight: real, value: real) {
  /* Predicados */

  /* 
  Predicado: verifica que el objeto es válido, es decir, que tiene valor y peso positivos.
  */
  ghost predicate Valid() {
    weight > 0.0 && value > 0.0
  }
}
