/*@ private normal_behavior
  @ requires true;
  @ ensures (\forall \bigint i;
  @     0 <= i < (\bigint)nodeList.length - (\bigint)1;
  @   (\forall \bigint j; i < j < nodeList.length;
  @     nodeList[i] != nodeList[j]));
  @*/
private /*@ strictly_pure @*/ void lemma_acyclic() {}