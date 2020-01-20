/*@
  @ public normal_behavior
  @   requires nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
  @   ensures
  @     nodeList == \seq_concat(\old(nodeList),
  @       \seq_singleton(nodeList[nodeList.length-1])) &&
  @     ((Node)nodeList[nodeList.length-1]).item == e &&
  @     \result;
  @ public exceptional_behavior
  @   requires nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @*/
public boolean add(/*@ nullable @*/ Object e) {
    checkSize(); // new
    linkLast(e);
    return true;
}