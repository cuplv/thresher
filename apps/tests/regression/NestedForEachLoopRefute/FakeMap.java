import java.util.List;
import java.util.LinkedList;
import java.util.HashMap;
import java.util.Map;

public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    class Account {
	public Account() { }
    }

    class Message {
	public Message() {

	}

	public Folder getFolder() { return new Folder(); }
    }

    class Folder {
	public Folder() { }

	public Account getAccount() { return new Account(); }
    }

    private void actOnMessages(Message[] messages, Object actor) {
        Map<Account, Map<Folder, List<Message>>> accountMap = new HashMap<Account, Map<Folder, List<Message>>>();

        for (Message message : messages) {
            Folder folder = message.getFolder();
            Account account = folder.getAccount();

            Map<Folder, List<Message>> folderMap = accountMap.get(account);
            if (folderMap == null) {
                folderMap = new HashMap<Folder, List<Message>>();
                accountMap.put(account, folderMap);
            }
            List<Message> messageList = folderMap.get(folder);
            if (messageList == null) {
                messageList = new LinkedList<Message>();
                folderMap.put(folder, messageList);
            }

            messageList.add(message);
        }
        for (Map.Entry<Account, Map<Folder, List<Message>>> entry : accountMap.entrySet()) {
            Account account = entry.getKey();

            //account.refresh(Preferences.getPreferences(K9.app));
            Map<Folder, List<Message>> folderMap = entry.getValue();
            for (Map.Entry<Folder, List<Message>> folderEntry : folderMap.entrySet()) {
                Folder folder = folderEntry.getKey();
                List<Message> messageList = folderEntry.getValue();
		actor.act(account, folder, messageList);
		foo(value);
            }
        }
    }

    static void foo(Object value) { }

    interface MessageActor {
        public void act(final Account account, final Folder folder, final List<Message> messages);
    }


    public Object put(String i, Object value) {
	actOnMessages(new Message[5], value);
	return null;
    }

    private void foo(Object value) {
	table[size] = value;
    }
}