public boolean remove(/*@ nullable @*/ Object o) {
    //@ ghost \bigint index = -1;
    if (o == null) {
        /*@ maintaining 0 <= (index + 1) &&
          @   (index + 1) <= nodeList.length;
          @ maintaining (\forall \bigint i; 0 <= i < (index + 1);
          @     ((Node)nodeList[i]).item != null);
          @ maintaining (index + 1) < nodeList.length ==>
          @   x == nodeList[index + 1];
          @ maintaining
          @   (index + 1) == nodeList.length <==> x == null;
          @ decreasing nodeList.length - (index + 1);
          @ assignable \strictly_nothing; */
        for (Node x = first; x != null; x = x.next) {
            //@ set index = index + 1;
            if (x.item == null) {
                //@ set nodeIndex = index;
                unlink(x);
                return true;
        }   }
    } else {
        /*@ maintaining 0 <= (index + 1) &&
          @   (index + 1) <= nodeList.length;
          @ maintaining (\forall \bigint i; 0 <= i < (index + 1);
          @     !o.equals(((Node)nodeList[i]).item));
          @ maintaining (index + 1) < nodeList.length ==>
          @   x == nodeList[index + 1];
          @ maintaining
          @   (index + 1) == nodeList.length <==> x == null;
          @ decreasing nodeList.length - (index + 1);
          @ assignable \strictly_nothing; */
        for (Node x = first; x != null; x = x.next) {
            //@ set index = index + 1;
            if (o.equals(x.item)) {
                //@ set nodeIndex = index;
                unlink(x);
                return true;
    }   }   }
    return false;
}