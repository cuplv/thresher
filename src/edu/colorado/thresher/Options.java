package edu.colorado.thresher;

import java.lang.annotation.*;
import java.lang.reflect.Field;

public class Options {

  @Retention(RetentionPolicy.RUNTIME)
  @interface boolOpt {
    String description();

    boolean _default();
  }

  @Retention(RetentionPolicy.RUNTIME)
  @interface intOpt {
    String description();

    int _default();
  }

  @Retention(RetentionPolicy.RUNTIME)
  @interface stringOpt {
    String description();

    String _default();
  }

  @boolOpt(description = "print debug information (LOTS of printing)", _default = false)
  public static boolean DEBUG = false;

  @boolOpt(description = "perform runtime assertion checks", _default = true)
  public static boolean CHECK_ASSERTS = true; // crashes when assertion checks
                                              // fail if true

  @boolOpt(description = "log extra info (very little printing. this should probably go away)", _default = true)
  public static boolean LOG = true; // log extra info (very little printing.
                                    // this should probably go away)

  @boolOpt(description = " print important output stats (probably shouldn't turn off)", _default = true)
  public static boolean PRINT = true; // print important output stats (probably
                                      // shouldn't turn off

  @boolOpt(description = "give up after assertion failure / crash", _default = true)
  public static boolean EXIT_ON_FAIL = true; // give up after assertion failure
                                             // / crash if true

  @boolOpt(description = "perform flow-insensitive points-to analysis only; don't do symbolic execution", _default = false)
  public static boolean FLOW_INSENSITIVE_ONLY = false; // if true, perform
                                                       // flow-insensitive
                                                       // points-to analysis
                                                       // only; don't do
                                                       // symbolic execution

  @boolOpt(description = "use piecewise symbolic executor. WARNING - under development", _default = false)
  public static boolean PIECEWISE_EXECUTION = false;

  @boolOpt(description = "perform callgraph pruning based on constraint set at function boundaries", _default = false)
  public static boolean CALLGRAPH_PRUNING = false;

  @boolOpt(description = "attempt to synthesize test cases for violations (currently unsupported)", _default = false)
  public static boolean SYNTHESIS = false;
  
  @boolOpt(description = "read WALA exclusions from config/exclusions.txt file", _default = true)
  public static boolean USE_EXCLUSIONS = true;

  @boolOpt(description = "prints end-to-end list of witnessed heap edges for witnessed error", _default = true)
  public static final boolean DUMP_WITNESSED_ERR_PATHS = true; // prints
                                                               // end-to-end
                                                               // list of
                                                               // witnessed
                                                               // errors in heap

  // if true, generate dependency rules for all statements in a method when we
  // generate rules for one statement in that method (cache all rules)
  // otherwise, generate dependency rules for each statement as we encounter it
  // (though for checking relevance of callees,
  // we still do whole-method rule generation)
  // @boolOpt(
  // description="generate dependency rules for all statements in a method when we generate rules for one statement in that method",
  // _default=false )
  public static final boolean GEN_DEPENDENCY_RULES_EAGERLY = false; // you want
                                                                    // this off
                                                                    // to be
                                                                    // fast

  @boolOpt(description = "use symbolic variables in dependency rules rather than doing a case split on concrete locations", _default = true)
  public static boolean ABSTRACT_DEPENDENCY_RULES = true; // you want this on to
                                                          // be fast

  // not currently enabled
  // @boolOpt
  // (description="do summaries do smart subsumption check (true), or dumb equality check (false)?",
  // _default=true )
  public static final boolean SUBSUMPTION_CHECK_AT_SUMMARIES = true; // you want
                                                                     // this on
                                                                     // to be
                                                                     // fast

  // not currently enabled
  // @boolOpt
  // (description="infer invariants for relevant loops? (alternative: drop all constraints produced in loop)",
  // _default=true)
  public static final boolean LOOP_INVARIANT_INFERENCE = true; // you want this
                                                               // on to be
                                                               // precise

  // not currently enabled
  // @boolOpt (description="keep full witness for each path", _default=true)
  public static boolean LOG_WITNESSES = false;
  
  @boolOpt (description="do summary check at function boundaries and loop heads", _default = true)
  public static boolean USE_SUMMARIES = true;

  @intOpt(description = "if the call stack is larger than this, we drop constraints that can be produced in callees rather than exploring them", _default = 2)
  public static int MAX_CALLSTACK_DEPTH = 2;

  @intOpt(description = "if the path constraints are larger than this, we (soundly) refuse to collect new constraints", _default = 2)
  // how large do we allow the path constraints to grow?
  public static int MAX_PATH_CONSTRAINT_SIZE = 2;

  @intOpt(description = "if we explore more paths than this while trying to refute/witness an edge, we report a timeout and (falsely) witness the edge", _default = 10000)
  public static int PATH_EXPLORE_LIMIT = 10000;

  @stringOpt(description = "usage: -app <path to directory of .class files to analyze>", _default = "")
  public static String APP;

  @stringOpt(description = "usage: -android_jar <path to jar file for version of android libraries>", _default = "android-2.3_annotated.jar")
  public static String ANDROID_JAR = "android/android-2.3_annotated.jar";

  @stringOpt(description = "run regression tests", _default = "")
  public static String REGRESSIONS;

  // if the paths to explore stack ever grows larger than this, we report a
  // timeout
  // TODO: not currently used
  // private static final int PATH_STACK_LIMIT = 1000;

  // consider paths that use weak references?
  public static boolean INCLUDE_WEAK_REFERENCES = false;

  // private static final boolean GEN_FLOW_INSENSITIVE_WITNESS = false; //
  // insist on generating flow-insensitive witness before doing symbolic
  // execution (TODO: doesn't work)

  // return path to dir to perform analyis on or _REGRESSION if regressions
  public static String parseArgs(String[] args) {
    if (args.length == 0)
      dumpHelpInfo();
    int index = 0;
    while (index < args.length) {
      String arg = args[index];
      if (arg == "") {
        index++;
        continue;
      } else if (arg.startsWith("-")) {
        boolean negate = false;
        if (arg.endsWith("!")) {
          negate = true;
          arg = arg.substring(0, arg.length() - 1);
        }
        // strip off "-"
        arg = arg.substring(1);
        // special cases
        if (arg.equals("help"))
          dumpHelpInfo();
        else if (arg.equals("regressions")) {
          APP = Main.REGRESSION;
          index++;
          continue;
        }
        // else, actually parsing options
        try {
          String upper = arg.toUpperCase();
          Field field = Options.class.getField(upper);
          if (field.getType().isAssignableFrom(Integer.TYPE)) {
            int newVal = Integer.parseInt(args[++index]);
            field.setInt(Options.class, newVal);
          } else if (field.getType().isAssignableFrom(Boolean.TYPE)) {
            field.setBoolean(Options.class, !negate);
          } else if (field.getType().isAssignableFrom(String.class)) {
            String newVal = args[++index];
            field.set(Options.class, newVal);
          }
        } catch (NoSuchFieldException e) {
          complain("Unrecognized option: " + arg);
        } catch (IllegalAccessException e) {
          complain("Can't write to field " + arg);
        } catch (Exception e) {
          complain("Bad or missing argument for option " + arg);
        }
      }
      index++;
    }
    return APP;
  }

  private static void dumpHelpInfo() {
    String optionStr = "USAGE: ./thresher.sh <options>. Use ! to negate boolean flags (e.g. -check_asserts!) \n";
    for (Field field : Options.class.getDeclaredFields()) {
      Annotation[] annots = field.getAnnotations();
      if (annots.length > 0) {
        if (annots[0] instanceof stringOpt) {
          stringOpt opt = (stringOpt) annots[0];
          optionStr += "-" + field.getName().toLowerCase() + "\t" + opt.description() + ".";
          if (opt._default() != null)
            optionStr += "\tdefault: " + opt._default();
          optionStr += "\n";
        } else if (annots[0] instanceof boolOpt) {
          boolOpt opt = (boolOpt) annots[0];
          optionStr += "-" + field.getName().toLowerCase() + "\t" + opt.description() + ".\tdefault: " + opt._default() + "\n";
        } else if (annots[0] instanceof intOpt) {
          intOpt opt = (intOpt) annots[0];
          optionStr += "-" + field.getName().toLowerCase() + "\t" + opt.description() + ".\tdefault: " + opt._default() + "\n";
        }
      }
    }
    System.out.println(optionStr.toString());
    System.exit(1);
  }

  private static void complain(String complaint) {
    System.out.println(complaint);
    System.exit(1);
  }
}
