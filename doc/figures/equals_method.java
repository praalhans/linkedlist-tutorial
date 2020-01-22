/*@ public normal_behavior
 @   requires true;
 @   ensures \result == self.equals(param0);
 @*/
public /*@ helper strictly_pure @*/
boolean equals(/*@ nullable @*/ Object param0);