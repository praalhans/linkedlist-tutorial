/*@
  @ private exceptional_behavior
  @   requires nodeList.length == Integer.MAX_VALUE;
  @   signals_only IllegalStateException;
  @   signals (IllegalStateException e) true;
  @ private normal_behavior
  @   requires nodeList.length != Integer.MAX_VALUE;
  @   ensures true;
  @*/