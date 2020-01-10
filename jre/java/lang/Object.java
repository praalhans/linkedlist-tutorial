package java.lang;

/**
 * @generated
 */
public class Object {
   /**
    * @generated
    */
   /*@ public normal_behavior
     @   requires true;
     @   ensures \result == self.equals(param0);
     @*/
   public /*@ helper strictly_pure @*/ boolean equals(/*@ nullable */ java.lang.Object param0);
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.lang.String toString();
}
