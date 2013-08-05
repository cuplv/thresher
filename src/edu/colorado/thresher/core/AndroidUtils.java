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

	public static void main(String[] args) {
		/*
		Collection<AndroidButton> buttons = parseButtonInfo(args[0]);
		for (AndroidButton button : buttons) {
			System.out.println("Button " + button);
		}*/
		
		buildSyntacticCG(args[0]);

		// inputs: list of external code callers (reflection, serializiation, ...), entrypoints?
		

	}
    /*	
    static class Util {
		public static Collection<File> listFilesRec(File startDir) {
			Util.Pre(startDir.isDirectory());
			Collection<File> files = new ArrayList<File>();
			
			final File[] genFiles = startDir.listFiles();
			for (File f : genFiles) {
				if (f.isDirectory()) {
					files.addAll(listFilesRec(f));
				} else { // is file
					files.add(f); 
				}
			}
			return files;
		}
		
		public static void Assert(boolean b, String s) {
			if (!b) {
				System.out.println("Failed assertion: " + s);
				Thread.dumpStack();
			}
		}
		
		public static void Assert(boolean b) {
			Assert(b, "");
		}
		
		public static void Unimp(String s) {
			Assert(false, s);
		}
		
		public static void Pre(boolean b) {
			Assert(b, "Failed precondition: ");
		}
	}

    // TMP!
    static class CGNode {

    }

    static class HashMapFactory {
	public static HashMap make() { return new LinkedHashMap(); }
    }

    static class HashSetFactory {
	public static HashSet make() { return new LinkedHashSet(); }
    }
    // END TMP
    */
  
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
	//+ " handler nodes " + Util.printCollection(eventHandlerNodes);
		;// TMP!
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
    
    parseIntIds(buttonIdMap, appPath); 
    
    // make sure we've found the labels and int id's for all buttons
    for (AndroidButton button : buttonIdMap.values()) {
      Util.Assert(button.label != null, "No label for button " + button.id);
      Util.Assert(button.intId != 0, "No id for button " + button);
    }
    
    return buttonIdMap.values();
  }
	
	static void parseStrings(Map<String,AndroidButton> buttonIdMap, String appPath) {
		final File valuesDir = new File(appPath + "res/values/strings.xml");
		Util.Assert(valuesDir.exists());
		
	}

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
		String path = appPath + "bin/classes";
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
	
  /**
   * read in R.java and populate the intId field of each button with its
   * identifier from R.java
   */
  // TODO: this is syntactic and quite hacky... but I don't think it's
  // a good idea to try to have WALA do it because it's very dependent
  // on string values
	static void parseInntIds(Map<String,AndroidButton> buttonIdMap, String appPath) {
    final String INT_DECL = "public static final int ";
    final String ID_CLASS = "public static final class id";
    final File genDir = new File(appPath + "gen/");
    Util.Assert(genDir.exists());
    final Collection<File> genFiles = Util.listFilesRec(genDir);
    
    for (File f : genFiles) {
      if (f.getName().equals("R.java")) {
        try {
          FileInputStream stream = new FileInputStream(f);
          BufferedReader br = new BufferedReader(new InputStreamReader(stream));
          String line;
          boolean parsing = false;
          while ((line = br.readLine()) != null) {
            //Util.Debug("line " + line);
            if (line.contains(ID_CLASS)) {
              parsing = true;
            } else if (parsing && line.contains("}")) parsing = false;
            
            if (parsing && line.contains(INT_DECL)) {
              line = line.replace(INT_DECL, "");
              // strip out spaces, tabs, and semicolons
              line =  line.replaceAll("[ \t;]", "");
              int eqIndex = line.indexOf("=");
              // get var name; should be between beginning of str and = sign
              String varName = line.substring(0, eqIndex);
              AndroidButton button = buttonIdMap.get(varName);
              if (button != null) {
                // parse out RHS of expression (part after = sign)
                line = line.substring(eqIndex + 1, line.length());
                int radix = 10;
                if (line.startsWith("0x")) {
                  // Java doesn't like parsing hexes that start with 0x. strip it out
                  line = line.substring(2, line.length());
                  radix = 16; // indicate that this is a hex value
                }
                Util.Assert(!line.contains("0x"));
                // get integer id assigned to button
                int intValue = Integer.parseInt(line, radix);
                button.intId = intValue;
              }
            }
          }
        } catch (FileNotFoundException e) {
          e.printStackTrace();
        } catch (IOException e) {
          e.printStackTrace();
        }
      }
    }
  }
    
  // TODO: should incorporate Activity name into button name...otherwise we might get
  // some extra matches in the case of unfortunate method names
  /*
  public static Map<String,String> parseButtonInfo(String appPath) {
    DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
    String[] handlerStrs = new String[] { "android:onClick" };
    Set<String> handlerNames = new LinkedHashSet<String>();
    for (int i = 0; i < handlerStrs.length; i++) handlerNames.add(handlerStrs[i]);
    // map from event handler name -> application methods that overrides event handler
    Map<String,String> applicationOverridesMap = new LinkedHashMap<String,String>();
    // map from button event handler -> string containing name for button
    Map<String,String> buttonNamesMap = new LinkedHashMap<String, String>();
    
    final String BUTTON_ID = "android:id";
    final String HANDLER_INDICATOR = "android:on";  
    final String BUTTON_NAME = "android:text";
    
    // for each file in res/layout
    final File layoutFolder = new File(appPath + "layout");
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
            if (map == null) continue;
            String handlerName = null;
            for (int j = 0; j < map.getLength(); j++) {
              Node node = map.item(j);
              String label = node.getNodeName();

              if (label.equals(BUTTON_ID)) {
                final String buttonId = node.getNodeValue();
                
              }
              
              if (handlerNames.contains(label)) {
                handlerName = node.getNodeValue();
                applicationOverridesMap.put(label, handlerName);
              } else if (label.startsWith(HANDLER_INDICATOR)) {
                Util.Unimp("possibly unknown handler " + label);
              }
  
              // TODO: need to associate node name with onClick; otherwise keys can stomp on each other
              
              if (label.equals(BUTTON_NAME)) {
                Util.Assert(handlerName != null, "handler should be defined here!");
                // add name of string containing button text to the map
                String link = node.getNodeValue().replace("@string/", "");
                buttonNamesMap.put(handlerName, link);
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
    }
    
    // read button strings from res/values/strings.xml
    try {
      DocumentBuilder db = dbf.newDocumentBuilder();
      Document doc = db.parse(appPath + "values/strings.xml");
      Element root = doc.getDocumentElement();
      // get all declared buttons
      NodeList nl = root.getElementsByTagName("string");
                  
      if (nl != null) {
        Set<String> assigned = HashSetFactory.make();
        for (int i = 0; i < nl.getLength(); i++) { // for each string
          Element el = (Element) nl.item(i);
          String name = el.getAttribute("name");
          String lab = null, newVal = null;
          for (String label : buttonNamesMap.keySet()) {
            if (name.equals(buttonNamesMap.get(label)) && assigned.add(label)) {
              lab = label;
              newVal = el.getTextContent();
            }
          }
          
          if (newVal != null) {
            buttonNamesMap.put(lab, newVal);
          }
        }
        // make sure we've found the names for all buttons
        for (String label : buttonNamesMap.keySet()) {
          if (!assigned.contains(label)) {
            Util.Assert(false, "Missing button label for handler " + label);
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

    return buttonNamesMap;
  }
  */
}
