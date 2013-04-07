package edu.colorado.thresher;

import java.util.Map;

import com.ibm.wala.analysis.typeInference.ConeType;
import com.ibm.wala.analysis.typeInference.PrimitiveType;
import com.ibm.wala.analysis.typeInference.TypeAbstraction;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.impl.AbstractRootMethod;
import com.ibm.wala.ipa.callgraph.impl.DefaultEntrypoint;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashMapFactory;

/**
 * An extension of the DefaultEntrypoint that re-uses receivers of similar types rather than
 * allocating a new receiver for each method call
 * 
 * For example, if we have a class C with methods foo() and bar(), using DefaultEntrypoint's
 * will yield IR:
 * v1 = new C
 * invoke foo v1
 * c2 = new C
 * invoke bar v2
 * 
 * whereas with SameReceiverEntrypoint's, we will get
 * v1 = new C
 * invoke foo v1
 * invoke bar v1
 * 
 * @author sam
 *
 */
public class SameReceiverEntrypoint extends DefaultEntrypoint {
  
  private static final Map<TypeReference,Integer> cachedReceivers = HashMapFactory.make();
    
  private final int RECEIVER = 0;
  
  public SameReceiverEntrypoint(IMethod method, IClassHierarchy cha) {
    super(method, cha);
  }

  private int getReceiver(TypeReference ref, AbstractRootMethod m) {
    Integer result = cachedReceivers.get(ref);
    int receiver;
    if (result == null) {
      // hack! needed for when WALA doesn't know how to create an instance of something
      try {
        // haven't seen a receiver of type ref yet; allocate a new one
        SSANewInstruction n = m.addAllocation(ref);
      //receiver = (n == null) ? -1 : n.getDef();
        receiver = n.getDef();
        cachedReceivers.put(ref, receiver);
      } catch (NullPointerException e) {
        return -1;
      }
    } else receiver = result.intValue();
    Util.Post(receiver != -1, "bad receiver");
    return receiver;
  }
 
  @Override
  protected int makeArgument(AbstractRootMethod m, int i) {
    TypeReference[] p = getParameterTypes(i);
    if (p.length == 0) {
      return -1;
    } else if (p.length == 1) {
      if (p[0].isPrimitiveType()) {
        return m.addLocal();
      } else {
        //SSANewInstruction n = m.addAllocation(p[0]);
        //return (n == null) ? -1 : n.getDef();
        return getReceiver(p[0], m);
      }
    } else {
      int[] values = new int[p.length];
      int countErrors = 0;
      for (int j = 0; j < p.length; j++) {
        int value;
        if (j == RECEIVER) {
          value = getReceiver(p[j], m);
        } else {
          // TODO: cache p[j] and don't add new allocation if we already have a cached version
          SSANewInstruction n = m.addAllocation(p[j]);
          value = (n == null) ? -1 : n.getDef();
        }
        if (value == -1) {
          countErrors++;
        } else {
          values[j - countErrors] = value;
        }
      }
      if (countErrors > 0) {
        int[] oldValues = values;
        values = new int[oldValues.length - countErrors];
        System.arraycopy(oldValues, 0, values, 0, values.length);
      }

      TypeAbstraction a;
      if (p[0].isPrimitiveType()) {
        a = PrimitiveType.getPrimitive(p[0]);
        for (i = 1; i < p.length; i++) {
          a = a.meet(PrimitiveType.getPrimitive(p[i]));
        }
      } else {
        IClassHierarchy cha = m.getClassHierarchy();
        IClass p0 = cha.lookupClass(p[0]);
        a = new ConeType(p0);
        for (i = 1; i < p.length; i++) {
          IClass pi = cha.lookupClass(p[i]);
          a = a.meet(new ConeType(pi));
        }
      }

      return m.addPhi(values);
    }
  }

}
