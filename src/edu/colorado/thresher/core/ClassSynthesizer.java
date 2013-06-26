package edu.colorado.thresher.core;

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
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.Selector;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.strings.Atom;

public class ClassSynthesizer {

  private static final String METHOD_SPACING = "  ";
  private static final String METHOD_BODY_SPACING = "    ";
  public static final String TEST_CLASS_NAME = "ThresherGeneratedTest";
  private static int counter = 0;
  private final IClassHierarchy cha;
  
  private final Map<IClass,Set<Atom>> alreadySynthesized = HashMapFactory.make();
  private final Map<IClass,List<String>> methodBodies = HashMapFactory.make();
  // map from type -> class name for our implementation of that type
  //private final Map<TypeReference,String> implementedInstances = HashMapFactory.make();
  private final Map<TypeName,String> implementedInstances = HashMapFactory.make();
  private final Collection<String> synthesizedClasses = new ArrayList<String>();

  
  public ClassSynthesizer(IClassHierarchy cha) {
    this.cha = cha;
  }
  
  /**
   * @param termValMap - input list of constraints 
   * @return - list of synthesized classes
   */
  public Collection<String> synthesize(Map<SimplePathTerm,String> termValMap) {
    // each term is an access path (e.g. x.f.g), where x, f, g are types.
    // the solver has given us a value of type g (say v) which may be a primitive
    // value or an instance. our remaining task is then to synthesize an  
    // an instance o_f of type f such that o_f.g = v, then synthesize an 
    // instance of_x of type x such that o_x.f = o_f, e.t.c
    
    // list of statements in generated test method that will call the user code
    List<String> testCode = new ArrayList<String>();
    
    // map from method -> {param index -> param value} map for that method
    //Map<IMethod,Map<Integer,Integer>> methodParamsMap = HashMapFactory.make();
    Map<IMethod,Map<Integer,String>> methodParamsMap = HashMapFactory.make();
    
    for (SimplePathTerm term : termValMap.keySet()) {
      // do we need to synthesize some method or field returning the value given in the map, or just pass the value?
      boolean synthesizeMethodOrField = false;
      List<FieldReference> fields = term.getFields();
      String instanceWithWrittenField = null;
      String extraMethodBody = null;
      if (fields != null) {
        for (int i = fields.size() - 1; i >= 0; i--) { // for each field from back to front
          FieldReference fld = fields.get(i);

          if (fld != null) {
            IClass clazz = cha.lookupClass(fld.getDeclaringClass());
            // is this a field or a method of the class?
            IField classField = clazz.getField(fld.getName());
            if (classField == null) {
              MethodReference method = MethodReference.findOrCreate(fld.getDeclaringClass(), 
                  Selector.make(fld.getName().toString()));
              
              String returnValue = termValMap.get(term);
              // typify the return value
              try {
                returnValue = synthesizeTypedValFromInt(Integer.parseInt(returnValue), method.getReturnType());
              } catch (NumberFormatException e) {
                // do nothing... this just means it was an instance
              }
              //if (returnValue.equals("0") && method.getReturnType().isReferenceType()) returnValue = "null";
              
              //String methodBody = synthesizeMethod(method, extraMethodBody, termValMap.get(term));
              String methodBody = synthesizeMethod(method, extraMethodBody, returnValue);
              synthesizeInterfaceMethod(methodBody, clazz, fld, term, termValMap);
              termValMap.put(term, synthesizeTypedValFromInt(1, method.getDeclaringClass()));
              // we're done with these variables now
              instanceWithWrittenField = null;
              extraMethodBody = null;
            } else {
              // need to synthesize field          
              // (1) synthesize an instance of this type
              // (2) find some way to write to the field
              if (!classField.isFinal() && !classField.isPrivate()) {
                // easy. just construct an instance, then write to the field directly
                String instance = synthesizeInstanceOf(clazz.getReference());
                Pair<String,String> pair = synthesizeAssignment(clazz.getReference(), instance);
                String fieldWrite = synthesizeFieldWrite(pair.fst, classField, termValMap.get(term));
                if (i == 0) {
                  // if we're writing a field of the base object (not a nested field)
                  testCode.add(pair.snd);
                  testCode.add(fieldWrite);
                }
                termValMap.put(term, pair.fst);
                // save the name of this instance and the code for the field write--we will need to synthesize a method that uses these 
                instanceWithWrittenField = pair.fst;
                extraMethodBody = METHOD_BODY_SPACING + pair.snd + '\n' + METHOD_BODY_SPACING + fieldWrite;
              } else {
                // perhaps not so easy...
                // just override the type and write the field there? this should work unless class in question is final
                // otherwise, kick off symbolic execution for each potential write to the field and figure out preconditions for the write
                Util.Unimp("field is private and/or final... not so obvious how to assign to it");
              }
            }
            synthesizeMethodOrField = true;
          }
        }
      }
      // we've worked all the way backward from the access path to the base pointer;
      // need to synthesize a test calling some method with this term passed as some param
      PointerKey key = term.getPointer();
      Util.Assert(key instanceof LocalPointerKey);
      // determine which param our term should be passed as
      int paramIndex = ((LocalPointerKey) key).getValueNumber() - 1;
      IMethod termMethod = term.getObject().getNode().getMethod();
      Util.Assert(termMethod.isPublic()); // can't call this method to pass our param unless it's public
      //Map<Integer,Integer> indexMap = methodParamsMap.get(termMethod);
      Map<Integer,String> indexMap = methodParamsMap.get(termMethod);
      if (indexMap == null) {
        indexMap = HashMapFactory.make();
        methodParamsMap.put(termMethod, indexMap);
      }
      // can't assign multiple values to same param
      //Util.Assert(!indexMap.containsKey(paramIndex) || ((synthesizeMethodOrField && indexMap.get(paramIndex) == 1) || 
                                                        //(!synthesizeMethodOrField && indexMap.get(paramIndex) == termValMap.get(term))));
      // bind the param index to the value of the term or to an instance of the synthesized class
      if (instanceWithWrittenField != null) indexMap.put(paramIndex, instanceWithWrittenField); // we created some instance and wrote to its field--pass that
      else if (!synthesizeMethodOrField) indexMap.put(paramIndex, termValMap.get(term) + ""); // convert int to string
      else indexMap.put(paramIndex, synthesizeTypedValFromInt(1, termMethod.getParameterType(paramIndex))); // create instance of synthesized class and bind
      // bind to already-created instance of synthesized class
    }
    
    // have synthesized implementations for all methods that matter. 
    // now, synthesize the rest of the methods and the class itself (needed for compilation)
    for (IClass clazz : methodBodies.keySet()) {
      //String newClassName = implementedInstances.get(clazz.getReference());
      String newClassName = implementedInstances.get(clazz.getReference().getName());
      Util.Assert(newClassName != null);
      String classText = synthesizeImplementsOrExtendsClass(newClassName, clazz);
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
  
  private void synthesizeInterfaceMethod(String body, IClass clazz, FieldReference fld, SimplePathTerm term, 
                                        Map<SimplePathTerm,String> termValMap) {
    MethodReference method = MethodReference.findOrCreate(fld.getDeclaringClass(), 
        Selector.make(fld.getName().toString()));
    if (Options.DEBUG) Util.Debug("synthesizing interface method " + method + " for " + clazz);
    
    Set<Atom> methodSet = alreadySynthesized.get(clazz);
    if (methodSet == null) {
      methodSet = HashSetFactory.make();
      alreadySynthesized.put(clazz, methodSet);
    }
    // have we already synthesized this method?
    if (!methodSet.add(method.getName())) return;
      
    // turn integer assignment from prover into String representation of typed object
    //String val = synthesizeTypedValFromInt(termValMap.get(term), method.getReturnType());
    String val = termValMap.get(term);
    if (body == null) body = synthesizeMethod(method, val);
    if (Options.DEBUG) Util.Debug("method body is " + body);
    
    List<String> methodBodiesForClass = methodBodies.get(clazz);
    if (methodBodiesForClass == null) {
      methodBodiesForClass = new ArrayList<String>();
      methodBodies.put(clazz, methodBodiesForClass);
    }
    methodBodiesForClass.add(body);

    if (!implementedInstances.containsKey(clazz.getReference().getName())) {
      String newClassName = getFreshClassName(clazz.getName().toString());
      implementedInstances.put(clazz.getReference().getName(), newClassName);  
    }
  }

  public void emitClass(String classText, String className, String path) {
    String fileName = path + className + ".java";
    // make sure we're not overwriting something
    Util.Assert(!new File(fileName).exists(), "Can't emit " + fileName + "; file already exists");
    Util.Print("Writing synthesized code to " + fileName);
    if (Options.DEBUG) Util.Debug("synthesized " + classText);
    PrintWriter out;
    try {
      out = new PrintWriter(fileName);
      out.write(classText);
      out.close();
    } catch (FileNotFoundException e) {
      Util.Print("Err " + e);
    }
  }

  private String synthesizeTestForConstraints(Map<IMethod,Map<Integer,String>> methodParamsMap) {
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
  
  private String synthesizeMethodCall(String receiver, IMethod method, Map<Integer,String> indexValMap) {
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
  
  private String synthesizeParamBinding(IMethod method, Map<Integer,String> indexValMap) {
    StringBuffer buf = new StringBuffer();
    buf.append('(');
    // skip first parameter; is always the receiver
    for (int i = 1; i < method.getNumberOfParameters(); i++) {
      TypeReference type = method.getParameterType(i);
      if (indexValMap.containsKey(i)) {
        //buf.append(synthesizeTypedValFromInt(indexValMap.get(i), type));
        buf.append(indexValMap.get(i));
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
  
  private String synthesizeConstructorCall(IMethod method, Map<Integer,String> indexValMap) {
    StringBuffer buf = new StringBuffer();
    buf.append("new ");
    buf.append(makeJavaTypeStringFromWALAType(method.getDeclaringClass().getReference()));
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
                                                    List<String> methods, Set<Atom> dontSynthesize) {
    String sig = synthesizeClassSignature(toImplement, newClassName);
    List<String> newMethods = synthesizeClassMethods(toImplement.getDeclaredMethods(), dontSynthesize);
    newMethods.addAll(methods);
    newMethods.add(synthesizeEmptyConstructor(newClassName));
    TypeName type = toImplement.getReference().getName();
    //Util.Assert(!implementedInstances.containsKey(type), 
      //  "already have instance of type " + type + ": " + implementedInstances.get(type));
    if (!implementedInstances.containsKey(type)) {
      implementedInstances.put(type, newClassName);
    }
    return synthesizeClass(sig, newMethods);
  }
  
  private String synthesizeImplementsOrExtendsClass(String newClassName, IClass toImplement) {
    List<String> methods = methodBodies.get(toImplement);
    if (methods == null) methods = Collections.EMPTY_LIST;
    Set<Atom> dontSynthesize = alreadySynthesized.get(toImplement);
        if (dontSynthesize == null) dontSynthesize = Collections.EMPTY_SET;
    return synthesizeImplementsOrExtendsClass(newClassName, toImplement, methods, dontSynthesize);
  }
  
  private List<String> synthesizeClassMethods(Collection<IMethod> methods, Set<Atom> dontSynthesize) {
    List<String> methodBodies = new ArrayList<String>();
    for (IMethod method : methods) {
      MethodReference ref = method.getReference();
      if (dontSynthesize.contains(ref.getName())) continue;
      
      if (Options.DEBUG) {
        Util.Debug("synthesizing " + method);
      }
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
      buf.append(makeJavaTypeStringFromWALAType(_interface.getReference()));
    }
    return buf.toString();
  }
  
  private String synthesizeMethod(MethodReference method, String retval) {
    return synthesizeMethod(method, null, retval);
  }
  
  private String synthesizeMethod(MethodReference method, String body, String retval) {
    String sig = synthesizeMethodSignature(method);
    String _return = synthesizeMethodReturn(method, retval);
    StringBuffer buf = new StringBuffer();
    buf.append(sig);
    buf.append(" {\n");
    if (body != null) {
      buf.append(body);
      buf.append('\n');
    }
    buf.append(_return);
    buf.append('\n');
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
  
  private String synthesizeMethodReturn(MethodReference method, String retval) {
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
    return makeJavaTypeStringFromWALAType(type);
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
      Util.Debug("have synthesized instance of " + type.getName() + "?");
      // first, check if we've synthesized some version of this. use that one if so.
      //String implemented = implementedInstances.get(type);
      String implemented = implementedInstances.get(type.getName());
      if (implemented != null) {
        // found our implementation; can create an instance using the empty constructor
        // this is safe because we always define the empty constructor for our synthesized classes
        return "new " + implemented + "()";
      }
      Util.Debug("false");
      
      // else, find existing implementations of it in scope
      Set<IClass> implementors = cha.getImplementors(type);
      Util.Assert(implementors.size() != 0, "Couldn't find implementor of " + type);  
      // try to find existing implementation...seems cheaper than synthesizing our own
      for (IClass impl : implementors) {
        if (!impl.isPublic()) {
          continue; // TODO: handle protected here
        }
        // TODO: use search heuristics here?
        // HACK! choose only application classes or java core library classes
        if (!impl.getName().toString().contains("java") && 
            impl.getClassLoader() != ClassLoaderReference.Application) {
          continue;
        }
        // avoid infinite recursion
        Util.Assert(!impl.getReference().equals(type));
        String instance = synthesizeInstanceOf(impl.getReference());
        if (instance != null) {
          //return makeCast(type, instance);
          return instance;
        }
      }
      // no implementations in scope; need to synthesize our own
      String newClassName = getFreshClassName(clazz.getName().toString());
      String classText = synthesizeImplementsOrExtendsClass(newClassName, clazz);
      emitClass(classText, newClassName, Options.APP);
      synthesizedClasses.add(newClassName);
      implementedInstances.put(type.getName(), newClassName);
      return "new " + newClassName + "()";
      // this call should now succeed
     // return synthesizeInstanceOf(type);
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
        buf.append(makeJavaTypeStringFromWALAType(type));
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
  
  // synthesize 'type name = rhs' assignment
  // returns var name, assignment code pair 
  private Pair<String,String> synthesizeAssignment(TypeReference type, String rhs) {
    StringBuffer buf = new StringBuffer();
    String name = makeFreshVarName(type);
    buf.append(makeJavaTypeStringFromWALAType(type)); 
    buf.append(' ');
    buf.append(name);
    buf.append(" = ");
    buf.append(rhs);
    buf.append(';');
    return Pair.make(name, buf.toString());
  }
  
  int varNameCounter = 0;
  private String makeFreshVarName(TypeReference type) {
    return type.getName().toString() + varNameCounter++;
  }
  
  // synthesize 'instance.field = value' field write
  private String synthesizeFieldWrite(String instance, IField field, String value) {
    StringBuffer buf = new StringBuffer();
    buf.append(instance);
    buf.append('.');
    buf.append(field.getName().toString());
    buf.append(" = ");
    //buf.append(synthesizeTypedValFromInt(value, field.getFieldTypeReference()));
    buf.append(value);
    buf.append(";");
    return buf.toString();
  }
  
  private String makeJavaTypeStringFromWALAType(TypeReference type) {
    String typeName = type.getName().toString();
    if (type.isArrayType()) {
      // parse out [ at the beginning of the name
      typeName = typeName.substring(1);
      // add brackets to end of name
      typeName += "[]";
    }
    // parse out the L at the beginning of the name
    String typeString = typeName.substring(1);
    typeString = typeString.replace("/", ".");
    return typeString.replace("$", ".");
  }
  
  private String makeCast(TypeReference castType, String castMe) {
    StringBuffer buf = new StringBuffer();
    buf.append("(");
    buf.append(makeJavaTypeStringFromWALAType(castType));
    buf.append(") ");
    buf.append(castMe);
    return buf.toString();
  }
  
}
