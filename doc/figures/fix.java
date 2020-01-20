    // new method, not in original LinkedList
    private void checkSize() {
        if (size == Integer.MAX_VALUE)
            throw new IllegalStateException(...);
    }