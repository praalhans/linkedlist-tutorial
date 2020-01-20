/*@ nullable @*/ transient Node first;
/*@ nullable @*/ transient Node last;
//@ private ghost \seq nodeList;
/*@ invariant
  @   nodeList.length == size &&
  @   nodeList.length <= Integer.MAX_VALUE &&
  @   (\forall \bigint i; 0 <= i < nodeList.length;
  @       nodeList[i] instanceof Node) &&
  @   ((nodeList == \seq_empty && first == null && last == null)
  @    || (nodeList != \seq_empty && first != null &&
  @         first.prev == null && last != null &&
  @         last.next == null && first == (Node)nodeList[0] &&
  @         last == (Node)nodeList[nodeList.length-1])) &&
  @   (\forall \bigint i; 0 < i < nodeList.length;
  @       ((Node)nodeList[i]).prev == (Node)nodeList[i-1]) &&
  @   (\forall \bigint i; 0 <= i < nodeList.length-1;
  @       ((Node)nodeList[i]).next == (Node)nodeList[i+1]);
  @*/