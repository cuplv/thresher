package edu.colorado.thresher.core;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.ArrayList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.classLoader.ClassFileModule;
import com.ibm.wala.shrikeCT.ClassConstants;
import com.ibm.wala.shrikeCT.ClassReader;
import com.ibm.wala.shrikeCT.ConstantPoolParser;
import com.ibm.wala.shrikeCT.ConstantValueReader;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.util.shrike.ShrikeClassReaderHandle;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;


public class AndroidUtils {

  /**
   * return a map from triggering event handler -> button text for each button 
   * 
   * @param appPath - path to some app's /res/ directory
   */
  
  private final static String DEFAULT_LISTENER = "onClick";

  static class AndroidButton {
    // unique identifier for the button
    final String id;
    // the integer the string id is mapped to
    int intId;
    // name of the method called when the button is clicked (normally onClick, but can be overridden)
    final String eventHandlerName;
    // event handler CGNode's. can be more than one because the manifest only specified a name; 
    // different Activities may provide different implementations for the method of that name 
    Set<CGNode> eventHandlerNodes;
    // name of the string that holds that button label
    final String buttonStringId;
    // text displayed on the button
    String label;

    // abstract memory cell corresponding to the button
    PointerVariable var;
    
    public AndroidButton(String id, String eventHandlerName, String buttonStringId) { 
      this.id = id;
      this.eventHandlerName = eventHandlerName;
      this.buttonStringId = buttonStringId;
      this.eventHandlerNodes = HashSetFactory.make();
    }
    
    public String toString() {
      return "ID: \"" + id + " " + intId + "\" Handler: \"" + eventHandlerName + "\" Label: \"" + label + "\" stringName: \"" + buttonStringId + "\"" 
          + " handler nodes " + Util.printCollection(eventHandlerNodes);
    }
        
    public boolean hasDefaultListener() {
      return DEFAULT_LISTENER.equals(eventHandlerName);
    }
    
  }
  
  // TODO: want id -> event handler -> button name mapping
  // TODO: handle volume button (and other hardware buttons), onTouch, e.t.c
  public static Collection<AndroidButton> parseButtonInfo(String appPath) {
    DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
    String[] handlerStrs = new String[] { "android:onClick" };
    Set<String> handlerNames = new LinkedHashSet<String>();
    for (int i = 0; i < handlerStrs.length; i++) {
      handlerNames.add(handlerStrs[i]);
    }

    // map from {string id name} -> button
    Map<String,AndroidButton> buttonStringMap = HashMapFactory.make();
    // map from {button id} -> button
    Map<String,AndroidButton> buttonIdMap = HashMapFactory.make();
    
    final String BUTTON_ID = "android:id";
    final String HANDLER_INDICATOR = "android:on";  
    final String BUTTON_NAME = "android:text";
    
    // for each file in res/layout
    final File layoutFolder = new File(appPath + "res/layout");
    final File[] layoutFiles = layoutFolder.listFiles();
    for (int f = 0; f < layoutFiles.length; f++) {
      if (!layoutFiles[f].getName().endsWith(".xml")) continue;
      try {
        DocumentBuilder db = dbf.newDocumentBuilder();
        Document doc = db.parse(layoutFiles[f]);
        Element root = doc.getDocumentElement();
        // get all declared buttons
        NodeList nl = root.getElementsByTagName("Button");
          
        if (nl != null) {
          for (int i = 0; i < nl.getLength(); i++) { // for each button
            Element el = (Element) nl.item(i);
            NamedNodeMap map = el.getAttributes();
            if (map == null) {
              continue;
            }
            String buttonId = null, handlerName = null, buttonStringId = null;
            
            for (int j = 0; j < map.getLength(); j++) { // for each attribute
              Node node = map.item(j);
              String label = node.getNodeName();
              if (label.equals(BUTTON_ID)) {
                buttonId = node.getNodeValue();
                buttonId = buttonId.replace("@+id/", "");
              } else if (handlerNames.contains(label)) {
                handlerName = node.getNodeValue();
              } else if (label.equals(BUTTON_NAME)) {
                buttonStringId = node.getNodeValue();
                buttonStringId = buttonStringId.replace("@string/", "");
              } else if (label.startsWith(HANDLER_INDICATOR)) {
                Util.Unimp("possibly unknown handler " + label);
              }
            }
            if (handlerName == null) {
              // button uses default handler onClick
              handlerName = DEFAULT_LISTENER;
            }
            Util.Assert(buttonId != null);
            Util.Assert(handlerName != null);
            Util.Assert(buttonStringId != null);
            AndroidButton button = new AndroidButton(buttonId, handlerName, buttonStringId);
            
            buttonStringMap.put(buttonStringId, button);
            buttonIdMap.put(buttonId, button);
          }
        }
      } catch(ParserConfigurationException pce) {
        pce.printStackTrace();
      } catch(SAXException se) {
        se.printStackTrace();
      } catch(IOException ioe) {
        ioe.printStackTrace();
      }
    }
    
    // read button strings from res/values/strings.xml
    try {
      DocumentBuilder db = dbf.newDocumentBuilder();
      Document doc = db.parse(appPath + "res/values/strings.xml");
      Element root = doc.getDocumentElement();
      // get all declared buttons
      NodeList nl = root.getElementsByTagName("string");
                  
      if (nl != null) {
        for (int i = 0; i < nl.getLength(); i++) { // for each string
          Element el = (Element) nl.item(i);
          String name = el.getAttribute("name");
          AndroidButton button = buttonStringMap.get(name);   
          if (button != null) {
            Util.Assert(button.label == null);
            button.label = el.getTextContent();
          }
        }
      }
    } catch(ParserConfigurationException pce) {
      pce.printStackTrace();
    } catch(SAXException se) {
      se.printStackTrace();
    } catch(IOException ioe) {
      ioe.printStackTrace();
    } 
    
    // read button id's from res/values/public.xml, if it exists
    File publicXML = new File(appPath + "res/values/public.xml");
    if (publicXML.exists()) {
      try {
        DocumentBuilder db = dbf.newDocumentBuilder();
        Document doc = db.parse(publicXML);
        Element root = doc.getDocumentElement();
        // get all button id's
        NodeList nl = root.getElementsByTagName("public");
                    
        if (nl != null) {
          for (int i = 0; i < nl.getLength(); i++) { // for each string
            Element el = (Element) nl.item(i);
            String type = el.getAttribute("type");
            if (type.equals("id")) {
              String name = el.getAttribute("name");
              AndroidButton button = buttonStringMap.get(name);   
              if (button != null) {
                // found the button; now get and parse its id
                String id = el.getAttribute("id");
                int radix = 10;
                if (id.startsWith("0x")) {
                  // Java doesn't like parsing hexes that start with 0x. strip it out
                  id = id.substring(2, id.length());
                  radix = 16; // indicate that this is a hex value
                }
                Util.Assert(!id.contains("0x"));
                // get integer id assigned to button
                int intValue = Integer.parseInt(id, radix);
                button.intId = intValue;
              }
            }
          }
        }
      } catch(ParserConfigurationException pce) {
        pce.printStackTrace();
      } catch(SAXException se) {
        se.printStackTrace();
      } catch(IOException ioe) {
        ioe.printStackTrace();
      } 
    } else {
      // otherwise, try to parse them from the .class files generated from R directly
      parseIntIds(buttonIdMap, appPath);
    }
    
    // make sure we've found the labels and int id's for all buttons
    for (AndroidButton button : buttonIdMap.values()) {
      Util.Assert(button.label != null, "No label for button " + button.id);
      Util.Assert(button.intId != 0, "No id for button " + button);
    }
    
    return buttonIdMap.values();
  }

  // copied from Shrike
	public static final byte CONSTANT_Integer = 3;
	
	static void buildSyntacticCG(String appPath) {
	  String path = appPath + "bin/classes";
	  final File binDir = new File(path);
	  Util.Assert(binDir.exists(), "can't find " + path);
	  final Collection<File> binFiles = Util.listFilesRec(binDir);
	  for (File f : binFiles) {
	    if (f.toString().endsWith(".class")) {
		  try {
		    ClassFileModule module = new ClassFileModule(f, null);
		    ShrikeClassReaderHandle handle = new ShrikeClassReaderHandle(module);
			ClassReader reader = handle.get();
			
			String clazz = reader.getName();
			Util.Print("class is " + clazz);
			ClassReader.AttrIterator iter = new ClassReader.AttrIterator();

			
			for (int i = 0; i < reader.getMethodCount(); i++) {
			  String name = reader.getMethodName(i);
			  String signature = reader.getMethodType(i);
			  Util.Print("method " + name);
			  Util.Print("sig " + signature);
				
			  reader.initMethodAttributeIterator(i, iter);
			  // iterate over code for method
			}
		  }
		  catch (InvalidClassFileException e) {
		    System.err.println("bad class file " + e);
		  }
		}
	  }
	}
	
   /**
	* find R$id.class, parse out button ID's from the constant pool using Shrike
	*/
	static void parseIntIds(Map<String,AndroidButton> buttonIdMap, String appPath) {
		String path = appPath + "bin";
		final File binDir = new File(path);
		Util.Assert(binDir.exists(), "can't find " + path);
		final Collection<File> binFiles = Util.listFilesRec(binDir);
		for (File f : binFiles) {
			String fileName = f.getName().toString();
			if (fileName.equals("R$id.class")) {
				// TODO: assert that class is an inner class of R.java
				try {
				    ClassFileModule module = new ClassFileModule(f, null);
					ShrikeClassReaderHandle handle = new ShrikeClassReaderHandle(module);
					ClassReader reader = handle.get();
					ConstantPoolParser cpParser = reader.getCP();
					ClassReader.AttrIterator iter = new ClassReader.AttrIterator();

					// for each field declared in the class
					for (int i = 0; i < reader.getFieldCount(); i++) {
						reader.initFieldAttributeIterator(i, iter);
						String name = reader.getFieldName(i);
						for (; iter.isValid(); iter.advance()) {
							reader.initFieldAttributeIterator(i, iter);
							if (iter.getName().equals("ConstantValue")) {
								ConstantValueReader cv = new ConstantValueReader(iter);
								AndroidButton button = buttonIdMap.get(name);
								int cpIndex = cv.getValueCPIndex();
								// if we have a button with the name of this field and the field type is an int,
								// then this field is the button ID
								if (button != null && cpParser.getItemType(cpIndex) == CONSTANT_Integer) {
									int fieldVal = cpParser.getCPInt(cpIndex);
									button.intId = fieldVal;
								}
							}
						}
					}				
				}
				catch (InvalidClassFileException e) {
					System.err.println("bad class file " + e);
				}
			}
		}
	}
}
