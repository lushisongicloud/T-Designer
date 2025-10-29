import javax.xml.parsers.DocumentBuilderFactory;
import org.w3c.dom.*;

public class FunctionCatalogParser {
    public static void main(String[] args) throws Exception {
        Document doc = DocumentBuilderFactory.newInstance()
                .newDocumentBuilder()
                .parse("QBT_function.xml");
        NodeList constraints = doc.getElementsByTagName("constraint");
        for (int i = 0; i < constraints.getLength(); i++) {
            Element constraint = (Element) constraints.item(i);
            String variable = constraint.getElementsByTagName("variable")
                    .item(0).getTextContent();
            String type = constraint.getElementsByTagName("type")
                    .item(0).getTextContent();
            System.out.println(variable + " -> [" + type + "]");
        }
    }
}
