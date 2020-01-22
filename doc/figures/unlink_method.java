/*@
  @ normal_behavior
  @   requires nodeList != \seq_empty &&
  @     0 <= nodeIndex < nodeList.length &&
  @     (Node)nodeList[nodeIndex] == x;
  @   ensures \result == \old(x.item) &&
  @     nodeList == \seq_concat(\old(nodeList)[0..nodeIndex],
  @       \old(nodeList)[nodeIndex+1..\old(nodeList).length]) &&
  @     nodeIndex == \old(nodeIndex);
  @*/
/*@ nullable @*/ Object unlink(Node x) {
    lemma_acyclic(); // new
    //@ set nodeList = \seq_concat(\dl_seqSub(nodeList,0,nodeIndex),
\dl_seqSub(nodeList,nodeIndex+1,\dl_seqLen(nodeList)));
    final Object element = x.item;
    final Node next = x.next;
    final Node prev = x.prev;
    ...