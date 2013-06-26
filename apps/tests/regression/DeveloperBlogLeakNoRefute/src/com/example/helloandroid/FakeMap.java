package com.example.helloandroid;

import java.io.Serializable;
import java.util.AbstractMap;
import java.util.LinkedList;
import java.util.Set;

public class FakeMap<K, V> extends AbstractMap<K, V> {//implements Cloneable, Serializable {
	private final static Object[] EMPTY_TABLE = new Object[0];
	
	private int size = 0;
	private int threshold;
	//private int index = 0;
	transient Object[] table;
	
	public FakeMap() {
		table = EMPTY_TABLE;
		//table = new Object[0];
		//table = new Object[0];
		//this.put((K) new Object(), (V) new Object());
		threshold = -1;
	}
	
	 @Override 
	 public V put(K key, V value) {
		Object tab[] = table;
		if (size++ > threshold) tab = doubleCapacity();
		addNewEntry(value);
		return null;
	}
	 
	 private Object[] doubleCapacity() {
		 threshold = size * 2;
		 Object[] newTable = makeTable();
		 return newTable;
	 }
	 
	 private Object[] makeTable() {
		 Object[] freshTable = new Object[threshold];
		 table = freshTable;
		 return freshTable;
	 }
	
	void addNewEntry(Object o) {
		table[size] = o;
	}
	
	public Set<Entry<K, V>> entrySet() {
		 return null;
	 }
	/*
	//private static final Entry[] EMPTY_TABLE = new FakeMapEntry[MINIMUM_CAPACITY >>> 1];
	//private Object[] EMPTY_TABLE = new Object[0];
	private static final Object[] EMPTY_TABLE = new Object[0];
	//private int index = 0;
	//transient FakeMapEntry<K, V>[] table;
	
	transient Object[] tableau;
	//transient Object[] tabloo;
	//transient LinkedList<Object> tableau;
	
	//private static Object EMPTY = new Object();
	//private Object tableau;
	
	public FakeMap(int i) {
	//	tableau = new Object[0];
	}
	
	public FakeMap() {
		//table = (FakeMapEntry<K, V>[]) EMPTY_TABLE;
		tableau = EMPTY_TABLE;
	//	tableau = new Object[0];
		//tableau = new LinkedList();
		//tableau = EMPTY;
	}
	 
	 @Override 
	 public V put(K key, V value) {
		//tableau[0] = value;
		//tabloo[0] = value;
		//tableau = value;
		// tableau = new LinkedList();
		// tableau.add(value);
		//addNewEntry(key, value, 0, 0);
		 if (tableau.length == 0) {
			 tableau = new Object[10];
		}
		//tableau[index++] = value;	
	    return null;
	}

	//void addNewEntry(K key, V value, int hash, int index) {
		//table[index] = new FakeMapEntry<K, V>(key, value, hash, table[index]);
		//tableau[index] = value;
	//}
	 
	 public Set<Entry<K, V>> entrySet() {
		 return null;
	 }
	 */
	/*
	static class FakeMapEntry<K, V> implements Entry<K, V> {
        final K key;
        V value;
        final int hash;
        FakeMapEntry<K, V> next;

        FakeMapEntry(K key, V value, int hash, FakeMapEntry<K, V> next) {
            this.key = key;
            this.value = value;
            this.hash = hash;
            this.next = next;
        }
        
        public final K getKey() {
            return key;
        }
        
        public final V getValue() {
            return value;
        }
        
        public final V setValue(V value) {
            V oldValue = this.value;
            this.value = value;
            return oldValue;
        }
	}
	*/
	
}
