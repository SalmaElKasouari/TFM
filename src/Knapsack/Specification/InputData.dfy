/*-----------------------------------------------------------------------------------------------------------------

El tipo InputData es el modelo de la representación formal de la entrada del problema de la mochila.

Estructura del fichero:

  Datatype
  - items: secuencia de objetos que tenemos a nuestra disposición (elementos de tipo ItemData).
  - maxWeight: peso máximo de la mochila.
  
  Predicados
    - Valid: una entrada es válida.

-----------------------------------------------------------------------------------------------------------------------*/


include "ItemData.dfy"


datatype InputData = InputData(items: seq<ItemData>, maxWeight: real) {
  
  /* Predicados */

  /* 
  Predicado: verifica que la entrada sea válida, es decir: 
    - todos los objetos son válidos, es decir, tienen valor y peso positivos.
    - el peso máximo de la mochila no es negativo.
  */
  ghost predicate Valid() {
    && (forall i | 0 <= i < |items| :: items[i].Valid())
    && maxWeight >= 0.0
  }
}