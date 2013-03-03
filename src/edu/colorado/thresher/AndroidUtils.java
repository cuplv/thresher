package edu.colorado.thresher;

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import com.ibm.wala.util.collections.HashSetFactory;

public class AndroidUtils {

  /**
   * return a map from triggering event handler -> button text for each button 
   * 
   * @param appPath - path to some app's /res/ directory
   */
  // TODO: should incorporate Activity name into button name...otherwise we might get
  // some extra matches in the case of unfortunate method names
  public static Map<String,String> parseButtonInfo(String appPath) {
    DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
    String[] handlerStrs = new String[] { "android:onClick" };
    Set<String> handlerNames = new LinkedHashSet<String>();
    for (int i = 0; i < handlerStrs.length; i++) handlerNames.add(handlerStrs[i]);
    // map from event handler name -> application methods that overrides event handler
    Map<String,String> applicationOverridesMap = new LinkedHashMap<String,String>();
    // map from button event handler -> string containing name for button
    Map<String,String> buttonNamesMap = new LinkedHashMap<String, String>();
    
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
              if (handlerNames.contains(label)) {
                handlerName = node.getNodeValue();
                applicationOverridesMap.put(label, handlerName);
              } else if (label.startsWith(HANDLER_INDICATOR)) {
                Util.Unimp("possibly unknown handler " + label);
              }
  
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
}
