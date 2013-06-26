package edu.colorado.thresher.external;

public class Assertions {  
  
 // Thresher-understood replacement for standard Java assert construct
 public static void Assert(boolean bool) {
   if (!bool) {
     // throw NullPointerException so we can have untracked Exception
     throw new NullPointerException("Failed assertion!");

     // don't want to do it this way because it makes building the pts-to graph expensive
     /*
     System.out.println("Failed assertion!");
     Thread.dumpStack();
     System.exit(1);
     */
   }
 }
}
