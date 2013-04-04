package edu.colorado.thresher;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.Selector;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;

public class ClassSynthesizer {

  private static final String METHOD_SPACING = "  ";
  private static final String METHOD_BODY_SPACING = "    ";
  private static int counter = 0;
  private final IClassHierarchy cha;
  
  public ClassSynthesizer(IClassHierarchy cha) {
    this.cha = cha;
  }
  
  public void synthesize(Map<SimplePathTerm,Integer> termValMap) {
    Map<IClass,Set<MethodReference>> alreadySynthesized = HashMapFactory.make();
    Map<IClass,List<String>> methodBodies = HashMapFactory.make();
    for (SimplePathTerm term : termValMap.keySet()) {
      FieldReference fld = term.getFirstField();
      IClass clazz = cha.lookupClass(fld.getDeclaringClass());
      MethodReference method = MethodReference.findOrCreate(fld.getDeclaringClass(), 
                                                            Selector.make(fld.getName().toString()));
      // turn integer assignment from prover into String representation of typed object
      String val = makeTypedValFromInt(termValMap.get(term), method.getReturnType());
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
    }
    
    // have synthesized implementations for all methods that matter. 
    // now, synthesize the rest of the methods and the class itself (needed for compilation)
    for (IClass clazz : methodBodies.keySet()) {
      String classText = synthesizeClass(clazz, methodBodies.get(clazz), alreadySynthesized.get(clazz));
      // TODO: emit into .java file
      Util.Print("\nSynthesized class:\n" + classText);
    }
  }
  
  private String synthesizeClass(IClass clazz, List<String> methodBodies, Set<MethodReference> dontSynthesize) {
    String newClassName = getFreshClassName(clazz.getName().toString());
    String sig = synthesizeClassSignature(clazz, newClassName);
    List<String> newMethodBodies = synthesizeClassMethods(clazz.getDeclaredMethods(), dontSynthesize);
    methodBodies.addAll(newMethodBodies);
    StringBuffer buf = new StringBuffer();
    buf.append(sig);
    buf.append(" {\n\n");
    for (String body : methodBodies) {
      buf.append(body);
      buf.append("\n");
    }
    buf.append("}\n");
    return buf.toString();
  }
  
  private List<String> synthesizeClassMethods(Collection<IMethod> methods, Set<MethodReference> dontSynthesize) {
    // TODO: synthesize constructor
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
  
  private String synthesizeClassSignature(IClass _interface, String newClassName) {
    // for now, only synthesizing interface implementations
    Util.Pre(_interface.isInterface()); 
    StringBuffer buf = new StringBuffer();
    if (_interface.isPublic()) buf.append("public ");
    else if (_interface.isPrivate()) buf.append("private ");
    buf.append("class ");
    buf.append(newClassName);
    buf.append(" implements ");
    // parse away 'L' at front of class name
    //buf.append(_interface.getName().toString().substring(1));
    buf.append(makejavaTypeStringFromWALAType(_interface.getReference()));
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
  
  private String makeTypedValFromInt(int i, TypeReference type) {
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
        String instance = makeInstanceOf(type);
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
  
  private String makeInstanceOf(TypeReference type) {
    StringBuffer buf = new StringBuffer();
    IClass clazz = cha.lookupClass(type);
    
    if (clazz.isInterface()) {
      // need to synthesize our own version of this, or find exisiting implementations of it in scope
      
    }
    
    Util.Assert(clazz != null);
    boolean found = false;
    // TODO: consider methods outside of this class as well
    for (IMethod method : clazz.getAllMethods()) {
      // TODO: handle protected correctly as well
      if (method.isPrivate() || method.isAbstract()) continue; // can't call this method to get our type
      if (method.isInit()) {
        // we have a constructor. now we must initialize each of its arguments
        buf.append("new ");
        buf.append(makejavaTypeStringFromWALAType(type));
        buf.append("(");
        // start at index 1 because constructors have an implicit parameter
        for (int i = 1; i < method.getNumberOfParameters(); i++) {
          TypeReference paramType = method.getParameterType(i); 
          Util.Assert(paramType != type); // prevent infinite recursion
          String param = makeInstanceOf(paramType);
          if (param == null) break; // couldn't construct an instance of this type
          buf.append(param);
          if (i != method.getNumberOfParameters() - 1) buf.append(", ");
        }
        buf.append(")");
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
  
}
