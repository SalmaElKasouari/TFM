include "Solution.dfy"

class PQData {
    var s : set<Solution>

    constructor PQData()
    {
      this.s := {};
    }
}