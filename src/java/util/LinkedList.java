package java.util;

public class LinkedList {

    transient int size = 0;
    transient Node first;
    transient Node last;
    
    public LinkedList() {}

    void linkLast(Object e) {
        final Node l = last;
        final Node newNode = new Node(l, e, null);
        last = newNode;
        if (l == null) first = newNode;
        else l.next = newNode;
        size++;
    }

    Object unlink(Node x) {
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

    // implements java.util.Collection.add
    public boolean add(Object e) {
        linkLast(e);
        return true;
    }

    // implements java.util.Collection.remove
    public boolean remove(Object o) {
        if (o == null) {
            for (Node x = first; x != null; x = x.next) {
                if (x.item == null) {
                    unlink(x);
                    return true;
                }
            }
        } else {
            for (Node x = first; x != null; x = x.next) {
                if (o.equals(x.item)) {
                    unlink(x);
                    return true;
                }
            }
        }
        return false;
    }

    private static class Node {
        Object item;
        Node next;
        Node prev;

        Node(Node prev, Object element, Node next) {
            this.item = element;
            this.next = next;
            this.prev = prev;
        }
    }

}

