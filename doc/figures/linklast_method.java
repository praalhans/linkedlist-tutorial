/*@
  @ normal_behavior
  @   requires
  @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\old(nodeList),
  @       \seq_singleton(nodeList[nodeList.length-1])) &&
  @     ((Node)nodeList[nodeList.length-1]).item == e;
  @*/
void linkLast(/*@ nullable @*/ Object e) {
    final Node l = last;
    final Node newNode = new Node(l, e, null);
    last = newNode;
    if (l == null) first = newNode;
    else l.next = newNode;
    size++;
    //@ set nodeList = \seq_concat(nodeList,\seq_singleton(last));
}