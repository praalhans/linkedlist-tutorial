/*@
  @ public normal_behavior
  @   requires true;
  @   ensures \result == false ==>
  @     (\forall \bigint i; 0 <= i < \old(nodeList.length);
  @     (o==null ==> \old(((Node)nodeList[i]).item) != null) &&
  @     (o!=null ==> !\old(o.equals(((Node)nodeList[i]).item)))) &&
  @     nodeList == \old(nodeList);
  @   ensures \result == true ==>
  @     (\exists \bigint j; 0 <= j < \old(nodeList.length);
  @       (\forall \bigint i; 0 <= i < j;
  @       (o==null ==> \old(((Node)nodeList[i]).item) != null) &&
  @       (o!=null ==> !\old(o.equals(((Node)nodeList[i]).item)))) &&
  @     nodeList == \seq_concat(\old(nodeList)[0..j],
  @       \old(nodeList)[j+1..\old(nodeList.length)]) &&
  @     (o==null ==> \old(((Node)nodeList[j]).item) == null) &&
  @     (o!=null ==> \old(o.equals(((Node)nodeList[j]).item))));
  @*/