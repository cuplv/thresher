package edu.colorado.thresher;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.Selector;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;

public class ClassSynthesizer {

  private static final String METHOD_SPACING = "  ";
  private static final String METHOD_BODY_SPACING = "    ";
  public static final String TEST_CLASS_NAME = "ThresherGeneratedTest";
  private static int counter = 0;
  private final IClassHierarchy cha;
  
  private final Map<IClass,Set<MethodReference>> alreadySynthesized = HashMapFactory.make();
  private final Map<IClass,List<String>> methodBodies = HashMapFactory.make();
  // map from type -> class name for our implementation of that type
  private final Map<TypeReference,String> implementedInstances = HashMapFactory.make();
  
  public ClassSynthesizer(IClassHierarchy cha) {
    this.cha = cha;
  }
  
  /**
   * @param termValMap - input list of constraints 
   * @return - list of synthesized classes
   */
  public Collection<String> synthesize(Map<SimplePathTerm,Integer> termValMap) {
    // each term is an access path (e.g. x.f.g), where x, f, g are types.
    // the solver has given us a value of type g (say v) which may be a primitive
    // value or an instance. our remaining task is then to synthesize an  
    // an instance o_f of type f such that o_f.g = v, then synthesize an 
    // instance of_x of type x such that o_x.f = o_f, e.t.c
    
    List<String> testCode = new ArrayList<String>();
    
    // map from method -> {param index -> param value} map for that method
    Map<IMethod,Map<Integer,Integer>> methodParamsMap = HashMapFactory.make();
    
    for (SimplePathTerm term : termValMap.keySet()) {
      FieldReference fld = term.getFirstField();
      boolean synthesizeInterface = fld != null;
      
      if (synthesizeInterface) {
        // need to synthesize an interface
        IClass clazz = cha.lookupClass(fld.getDeclaringClass());
        MethodReference method = MethodReference.findOrCreate(fld.getDeclaringClass(), 
                                                              Selector.make(fld.getName().toString()));
        // turn integer assignment from prover into String representation of typed object
        String val = synthesizeTypedValFromInt(termValMap.get(term), method.getReturnType());
        String methodBody = synthesizeMethod(method, val);
        Set<MethodReference> methodSet = alreadySynthesized.get(clazz);
        if (methodSet == null) {
          methodSet = HashSetFactory.make();
          alreadySynthesized.put(clazz, methodSet);
        }
        methodSet.add(method);
        
        List<String> methodBodiesForClass = methodBodies.get(clazz);
        if (methodBodiesForClass == null) {
          methodBodiesForClass = new ArrayList<String>();
          methodBodies.put(clazz, methodBodiesForClass);
        }
        methodBodiesForClass.add(methodBody);
        if (!implementedInstances.containsKey(clazz.getReference())) {
          String newClassName = getFreshClassName(clazz.getName().toString());
          implementedInstances.put(clazz.getReference(), newClassName);  
        }
      }

      // need to synthesize a test calling some method with this term passed as some param
      PointerKey key = term.getPointer();
      Util.Assert(key instanceof LocalPointerKey);
      // determine which param our term should be passed as
      int paramIndex = ((LocalPointerKey) key).getValueNumber() - 1;
      IMethod termMethod = term.getObject().getNode().getMethod();
      Util.Assert(termMethod.isPublic()); // can't call this method to pass our param unless it's public
      Map<Integer,Integer> indexMap = methodParamsMap.get(termMethod);
      if (indexMap == null) {
        indexMap = HashMapFactory.make();
        methodParamsMap.put(termMethod, indexMap);
      }
      // can't assign multiple values to same param
      Util.Assert(!indexMap.containsKey(paramIndex) || ((synthesizeInterface && indexMap.get(paramIndex) == 1) || 
                                                        (!synthesizeInterface && indexMap.get(paramIndex) == termValMap.get(term))));
      // bind the param index to the value of the term
      if (!synthesizeInterface) indexMap.put(paramIndex, termValMap.get(term));
      else indexMap.put(paramIndex, 1); // bind to instance of synthesized class
    }
    
    Collection<String> synthesizedClasses = new ArrayList<String>();
    // have synthesized implementations for all methods that matter. 
    // now, synthesize the rest of the methods and the class itself (needed for compilation)
    for (IClass clazz : methodBodies.keySet()) {
      //String newClassName = getFreshClassName(clazz.getName().toString());
      String newClassName = implementedInstances.get(clazz.getReference());
      Util.Assert(newClassName != null);
      String classText = synthesizeImplementsOrExtendsClass(newClassName, clazz, methodBodies.get(clazz), alreadySynthesized.get(clazz));
      emitClass(classText, newClassName, Options.APP);
      synthesizedClasses.add(newClassName);
    }
    testCode.add(synthesizeTestForConstraints(methodParamsMap));
    // synthesize test class
    String classBody = synthesizeTestMethod(testCode);
    String classText = synthesizeNewClass(TEST_CLASS_NAME, Collections.singletonList(classBody));
    emitClass(classText, TEST_CLASS_NAME, Options.APP);
    synthesizedClasses.add(TEST_CLASS_NAME);
    return synthesizedClasses;
  }

  public void emitClass(String classText, String className, String path) {
    String fileName = path + className + ".java";
    // make sure we're not overwriting something
    Util.Assert(!new File(fileName).exists());
    Util.Print("Writing synthesized code to " + fileName);
    PrintWriter out;
    try {
      out = new PrintWriter(fileName);
      out.write(classText);
      out.close();
    } catch (FileNotFoundException e) {
      Util.Print("Err " + e);
    }
  }

  private String synthesizeTestForConstraints(Map<IMethod,Map<Integer,Integer>> methodParamsMap) {
    StringBuffer buf = new StringBuffer();
    for (IMethod method : methodParamsMap.keySet()) {
      IClass clazz = method.getDeclaringClass();
      
      if (method.isStatic()) {
        // don't need to create an instance of the class; can call method directly
        buf.append(synthesizeMethodCall(clazz.getName().toString(), method, methodParamsMap.get(method)));
      } else if (method.isInit()) {
        buf.append(synthesizeConstructorCall(method, methodParamsMap.get(method)));
      } else {
        // need to create an instance of the class, then call a method on it
        String instance = synthesizeInstanceOf(clazz.getReference());
        buf.append(synthesizeMethodCall(instance, method, methodParamsMap.get(method)));
      }
    }
    return buf.toString();
  }
  
  private String synthesizeMethodCall(String receiver, IMethod method, Map<Integer,Integer> indexValMap) {
    StringBuffer buf = new StringBuffer();
    buf.append(receiver);
    buf.append('.');
    buf.append(method.getName());
    buf.append(synthesizeParamBinding(method, indexValMap));
    buf.append(';');
    return buf.toString();
  }
  
  private String synthesizeParamBinding(IMethod method) {
    return synthesizeParamBinding(method, Collections.EMPTY_MAP);
  }
  
  private String synthesizeParamBinding(IMethod method, Map<Integer,Integer> indexValMap) {
    StringBuffer buf = new StringBuffer();
    buf.append('(');
    // skip first parameter; is always the receiver
    for (int i = 1; i < method.getNumberOfParameters(); i++) {
      TypeReference type = method.getParameterType(i);
      if (indexValMap.containsKey(i)) {
        buf.append(synthesizeTypedValFromInt(indexValMap.get(i), type));
      } else {
        if (type.isPrimitiveType()) {
          buf.append(synthesizeDefaultValue(type));
        } else {
          // TODO: should we synthesize default value instead?
          buf.append(synthesizeInstanceOf(type));
        }
      }
      if (i != method.getNumberOfParameters() - 1) buf.append(", ");
    }
    buf.append(")");
    return buf.toString();
  }
  
  private String synthesizeConstructorCall(IMethod method, Map<Integer,Integer> indexValMap) {
    StringBuffer buf = new StringBuffer();
    buf.append("new ");
    buf.append(makejavaTypeStringFromWALAType(method.getDeclaringClass().getReference()));
    buf.append(synthesizeParamBinding(method, indexValMap));
    buf.append(';');
    return buf.toString();
  }
  
  private String synthesizeTestMethod(List<String> testCode) {
    final String MAIN = METHOD_SPACING + "public static void main(String[] args) {\n";
    StringBuffer buf = new StringBuffer();
    buf.append(MAIN);
    for (String test : testCode) {
      buf.append(METHOD_BODY_SPACING + test);
      buf.append("\n");
    }
    buf.append(METHOD_SPACING + "}\n");
    return buf.toString();
  }
  
  private String synthesizeNewClass(String newClassName, List<String> methods) {
    String signature = synthesizeClassSignature(newClassName);
    return synthesizeClass(signature, methods);
  }
  
  public String synthesizeClass(String signature, List<String> methods) {
    StringBuffer buf = new StringBuffer();
    buf.append(signature);
    buf.append(" {\n\n");
    for (String body : methods) {
      buf.append(body);
      buf.append("\n");
    }
    buf.append("}\n");
    return buf.toString();
  }
  
  /**
   * synthesize implementation of interface or class that extends existing class
   * @param toImplement - interface to implement or class to extend
   * @param methods - text of methods that have already been synthesized
   * @param dontSynthesize - list of method bodies that have already been synthesized
   * @return - ready-to-compile string representation of class
   */
  private String synthesizeImplementsOrExtendsClass(String newClassName, IClass toImplement, 
                                                    List<String> methods, Set<MethodReference> dontSynthesize) {
    String sig = synthesizeClassSignature(toImplement, newClassName);
    List<String> newMethods = synthesizeClassMethods(toImplement.getDeclaredMethods(), dontSynthesize);
    methods.addAll(newMethods);
    methods.add(synthesizeEmptyConstructor(newClassName));
    return synthesizeClass(sig, methods);
  }
  
  private List<String> synthesizeClassMethods(Collection<IMethod> methods, Set<MethodReference> dontSynthesize) {
    List<String> methodBodies = new ArrayList<String>();
    for (IMethod method : methods) {
      MethodReference ref = method.getReference();
      if (dontSynthesize.contains(ref)) continue;
      
      String val = null;
      if (method.getReturnType() != TypeReference.Void) {
        // get default value of return type
        val = synthesizeDefaultValue(method.getReturnType());
      } // else, no return value needed
      methodBodies.add(synthesizeMethod(ref, val));
    }
    return methodBodies;
  }
  
  private String synthesizeEmptyConstructor(String className) {
    StringBuffer buf = new StringBuffer();
    buf.append(METHOD_SPACING);
    buf.append("public ");
    buf.append(className);
    buf.append("() {}");
    return buf.toString();
  }
  
  private String synthesizeClassSignature(String newClassName) {
    return synthesizeClassSignature(null, newClassName);
  }
  
  private String synthesizeClassSignature(IClass _interface, String newClassName) {
    // for now, not synthesizing overrides
    Util.Pre(_interface == null || _interface.isInterface()); 
    StringBuffer buf = new StringBuffer();
    buf.append("public ");
    buf.append("class ");
    buf.append(newClassName);
    if (_interface != null) {
      buf.append(" implements ");
      buf.append(makejavaTypeStringFromWALAType(_interface.getReference()));
    }
    return buf.toString();
  }
  
  private String synthesizeMethod(MethodReference method, String retval) {
    String sig = synthesizeMethodSignature(method);
    String body = synthesizeMethodBody(method, retval);
    StringBuffer buf = new StringBuffer();
    buf.append(sig + " {\n");
    buf.append(body + "\n");
    buf.append(METHOD_SPACING);
    buf.append("}\n");
    return buf.toString();
  }

  // TODO: how do we get method access levels?
  private String synthesizeMethodSignature(MethodReference method) {
    StringBuffer buf = new StringBuffer();
    buf.append(METHOD_SPACING);
    buf.append("public ");
    buf.append(synthesizeType(method.getReturnType()));
    buf.append(" " + method.getName());
    buf.append("(");
    for (int i = 0; i < method.getNumberOfParameters(); i++) {
      buf.append(synthesizeType(method.getParameterType(i)));
      buf.append(" param" + i); // make fresh name
      if (i != method.getNumberOfParameters() - 1) buf.append(", ");
    }
    buf.append(")");
    return buf.toString();
  }
  
  private String synthesizeMethodBody(MethodReference method, String retval) {
    StringBuffer buf = new StringBuffer();
    if (retval != null) { // null return value means this is a void method
      buf.append(METHOD_BODY_SPACING);
      buf.append("return ");
      buf.append(retval);
      buf.append(';');
    } else Util.Assert(method.getReturnType() == TypeReference.Void);
    return buf.toString();
  }
  
  private String synthesizeType(TypeReference type) {
    if (type.isPrimitiveType()) return synthesizePrimitiveType(type);
    return makejavaTypeStringFromWALAType(type);
  }
  
  private String synthesizePrimitiveType(TypeReference type) {
    StringBuffer buf = new StringBuffer();
    if (type == TypeReference.Int) {
      buf.append("int");
    } else if (type == TypeReference.Boolean) {
      buf.append("boolean");
    } else if (type == TypeReference.Void) {
      buf.append("void");
    } else Util.Unimp("unsupported primitive " + type);
    return buf.toString();
  }
  
  // HACK! let the compiler tell us what the default values are
  private static Object DEFAULT_OBJ;
  private static int DEFAULT_INT;
  private static boolean DEFAULT_BOOL;
  
  private String synthesizeDefaultValue(TypeReference type) {
    if (type.isReferenceType()) return "" + DEFAULT_OBJ;
    else if (type.isPrimitiveType()) {
      if (type == TypeReference.Int) return "" + DEFAULT_INT;
      else if (type == TypeReference.Boolean) return "" + DEFAULT_BOOL;
      else Util.Unimp("unsupported primitive type " + type);
    } else Util.Unimp("unhandled type " + type);
    return null;
  }
  
  private String synthesizeTypedValFromInt(int i, TypeReference type) {
    StringBuffer buf = new StringBuffer();
    if (type.isPrimitiveType()) {
      if (type == TypeReference.Int) {
        buf.append(i);
      } else if (type == TypeReference.Boolean) {
        if (i == 0) buf.append("false");
        else buf.append("true");
      } else Util.Unimp("unsupported primitive type " + type);
    } else if (type.isReferenceType()) { 
      if (i == 0) buf.append("null");
      else {
        String instance = synthesizeInstanceOf(type);
        Util.Assert(instance != null, "Couldn't make instance of desired type " + type);
        buf.append(instance);
      }
    } else Util.Unimp("unhandled type " + type);
    return buf.toString();
  }
  
  private String getFreshClassName(String name) {
    // parse out 'L' at beginning
    String parsed = name.substring(1);
    // parse out package name
    while (parsed.indexOf('/') != -1) {
      parsed = parsed.substring(parsed.indexOf('/') + 1);
    }
    return parsed + "Impl" + counter++;
  }
  
  private String synthesizeInstanceOf(TypeReference type) {
    StringBuffer buf = new StringBuffer();
    IClass clazz = cha.lookupClass(type);
    Util.Assert(clazz != null, "couldn't find class for " + type);
    
    if (clazz.isInterface()) {
      // first, check if we've synthesized some version of this. use that one if so.
      String implemented = implementedInstances.get(type);
      if (implemented != null) {
        // found our implementation; can create an instance using the empty constructor
        // this is safe because we always define the empty constructor for our synthesized classes
        return "new " + implemented + "()";
      }
      
      // else, find existing implementations of it in scope
      Set<IClass> implementors = cha.getImplementors(type);
      Util.Assert(implementors.size() != 0);  
      // try to find existing implementation...seems cheaper than synthesizing our own
      for (IClass impl : implementors) {
        if (!impl.isPublic()) continue; // TODO: handle protected here
        // TODO: use search heuristics here?
        // HACK! choose only application classes or java core library classes
        if (!impl.getName().toString().contains("java") && 
            impl.getClassLoader() != ClassLoaderReference.Application) {
          continue;
        }
        String instance = synthesizeInstanceOf(impl.getReference());
        if (instance != null) {
          //return makeCast(type, instance);
          return instance;
        }
      }
      Util.Unimp("synthesizing instance of interface class " + clazz);
    } else if (clazz.isAbstract()) {
      Util.Unimp("synthesizing instance abstract class " + clazz);
    }
    
    Util.Assert(clazz != null);
    boolean found = false;
    // TODO: consider methods outside of this class as well
    for (IMethod method : clazz.getAllMethods()) {
      // TODO: handle protected correctly as well
      //if (method.isPrivate() || method.isAbstract()) continue; // can't call this method to get our type
      if (!method.isPublic()) continue; // can't call this method to get our type
      if (method.isInit()) {
        // we have a constructor. now we must initialize each of its arguments
        buf.append("new ");
        buf.append(makejavaTypeStringFromWALAType(type));
        buf.append(synthesizeParamBinding(method));
        found = true;
        break;
      } else if (method.isStatic() && method.getReturnType() == type) { // TODO: handle subtyping
        // we have a method returning our desired type. we must initialize each of its arguments
        Util.Unimp("static methods");
        found = true;
        break;
      } // else, this method isn't useful to us
    }
    if (found) return buf.toString(); // was able to construct the type; done
    return null; // couldn't find a way to construct this type
  }
  
  private String makejavaTypeStringFromWALAType(TypeReference type) {
    // parse out the L at the beginning of the name
    String typeString = type.getName().toString().substring(1);
    return typeString.replace("/", ".");
  }
  
  private String makeCast(TypeReference castType, String castMe) {
    StringBuffer buf = new StringBuffer();
    buf.append("(");
    buf.append(makejavaTypeStringFromWALAType(castType));
    buf.append(") ");
    buf.append(castMe);
    return buf.toString();
  }
  
}
