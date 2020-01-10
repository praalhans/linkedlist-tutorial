package java.util;

public class LinkedList {

    transient int size = 0;
    /*@ nullable @*/ transient Node first;
    /*@ nullable @*/ transient Node last;
    //@ private ghost \seq nodeList;
    //@ private ghost \bigint nodeIndex;

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

    /*@
      @ public normal_behavior
      @   ensures nodeList == \seq_empty;
      @*/
    public BoundedLinkedList() {}

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

    /*@ private normal_behavior
      @ requires true;
      @ ensures (\forall \bigint i; 0 <= i < (\bigint)nodeList.length - (\bigint)1;
      @   (\forall \bigint j; i < j < nodeList.length;
      @     nodeList[i] != nodeList[j]));
      @*/
    private /*@ strictly_pure @*/ void lemma_acyclic() {}

    /*@
      @ normal_behavior
      @   requires
      @     nodeList != \seq_empty &&
      @     0 <= nodeIndex < nodeList.length &&
      @     (Node)nodeList[nodeIndex] == x;
      @   ensures
      @     \result == \old(x.item) &&
      @     nodeList == \seq_concat(\old(nodeList)[0..nodeIndex],
      @       \old(nodeList)[nodeIndex+1..\old(nodeList).length]) &&
      @     nodeIndex == \old(nodeIndex);
      @*/
    /*@ nullable @*/ Object unlink(Node x) {
        //@ set nodeList = \seq_concat(\dl_seqSub(nodeList,0,nodeIndex), \dl_seqSub(nodeList,nodeIndex+1,\dl_seqLen(nodeList)));
        final Object element = x.item;
        final Node next = x.next;
        final Node prev = x.prev;
        if (prev == null) {first = next;}
        else {
            prev.next = next;
            x.prev = null;
        }
        if (next == null) {last = prev;}
        else {
            next.prev = prev;
            x.next = null;
        }
        x.item = null;
        size--;
        return element;
    }

    // new method, not in original LinkedList
    /*@
      @ private exceptional_behavior
      @   requires nodeList.length == Integer.MAX_VALUE;
      @   signals_only IllegalStateException;
      @   signals (IllegalStateException e) true;
      @ private normal_behavior
      @   requires nodeList.length != Integer.MAX_VALUE;
      @   ensures true;
      @*/
    private /*@ strictly_pure @*/ void checkSize() {
        if (size == Integer.MAX_VALUE)
            throw new IllegalStateException("Not enough space left in List to add new elements");
    }

    // implements java.util.Collection.add
    /*@
      @ public normal_behavior
      @   requires
      @     nodeList.length + (\bigint)1 <= Integer.MAX_VALUE;
      @   ensures
      @     nodeList == \seq_concat(\old(nodeList),
      @       \seq_singleton(nodeList[nodeList.length-1])) &&
      @     ((Node)nodeList[nodeList.length-1]).item == e &&
      @     \result;
      @ public exceptional_behavior
      @   requires
      @     nodeList.length == Integer.MAX_VALUE;
      @   signals_only IllegalStateException;
      @   signals (IllegalStateException e) true;
      @*/
    public boolean add(/*@ nullable @*/ Object e) {
        checkSize(); // new
        linkLast(e);
        return true;
    }

    // implements java.util.Collection.remove
    /*@
      @ public normal_behavior
      @   requires o == null;
      @   ensures
      @     \result == false ==>
      @       (\forall \bigint i; 0 <= i < \old(nodeList.length);
      @         \old(((Node)nodeList[i]).item) != null) &&
      @       nodeList == \old(nodeList);
      @   ensures
      @     \result == true ==>
      @       (\exists \bigint j; 0 <= j < \old(nodeList.length);
      @         (\forall \bigint i; 0 <= i < j;
      @           \old(((Node)nodeList[i]).item) != null) &&
      @         nodeList == \seq_concat(\old(nodeList)[0..j],
      @           \old(nodeList)[j+1..\old(nodeList.length)]) &&
      @         \old(((Node)nodeList[j]).item) == null);
      @ public normal_behavior
      @   requires o != null;
      @   ensures
      @     \result == false ==>
      @       (\forall \bigint i; 0 <= i < \old(nodeList.length);
      @         !\old(o.equals(((Node)nodeList[i]).item))) &&
      @       nodeList == \old(nodeList);
      @   ensures
      @     \result == true ==>
      @       (\exists \bigint j; 0 <= j < \old(nodeList.length);
      @         (\forall \bigint i; 0 <= i < j;
      @           !\old(o.equals(((Node)nodeList[i]).item))) &&
      @         nodeList == \seq_concat(\old(nodeList)[0..j],
      @           \old(nodeList)[j+1..\old(nodeList.length)]) &&
      @       \old(o.equals(((Node)nodeList[j]).item)));
      @*/
    public boolean remove(/*@ nullable @*/ Object o) {
        //@ ghost \bigint index = -1;
        if (o == null) {
            /*@
              @ maintaining
              @   0 <= (index + 1) &&
              @   (index + 1) <= nodeList.length;
              @ maintaining
              @   (\forall \bigint i; 0 <= i < (index + 1);
              @       ((Node)nodeList[i]).item != null);
              @ maintaining
              @   (index + 1) < nodeList.length ==>
              @     x == nodeList[index + 1];
              @ maintaining
              @   (index + 1) == nodeList.length <==>
              @   x == null;
              @ decreasing
              @   nodeList.length - (index + 1);
              @ assignable
              @   \strictly_nothing;
              @*/
            for (Node x = first; x != null; x = x.next) {
                //@ set index = index + 1;
                if (x.item == null) {
                    //@ set nodeIndex = index;
                    unlink(x);
                    return true;
                }
            }
        } else {
            /*@
              @ maintaining
              @   0 <= (index + 1) &&
              @   (index + 1) <= nodeList.length;
              @ maintaining
              @   (\forall \bigint i; 0 <= i < (index + 1);
              @       !o.equals(((Node)nodeList[i]).item));
              @ maintaining
              @   (index + 1) < nodeList.length ==>
              @     x == nodeList[index + 1];
              @ maintaining
              @   (index + 1) == nodeList.length <==>
              @   x == null;
              @ decreasing
              @   nodeList.length - (index + 1);
              @ assignable
              @   \strictly_nothing;
              @*/
            for (Node x = first; x != null; x = x.next) {
                //@ set index = index + 1;
                if (o.equals(x.item)) {
                    //@ set nodeIndex = index;
                    unlink(x);
                    return true;
                }
            }
        }
        return false;
    }

    private static class Node {
        /*@ nullable @*/ Object item;
        /*@ nullable @*/ Node next;
        /*@ nullable @*/ Node prev;

        Node(/*@ nullable @*/ Node prev,
        /*@ nullable @*/ Object element,
        /*@ nullable @*/ Node next) {
            this.item = element;
            this.next = next;
            this.prev = prev;
        }
    }

}

