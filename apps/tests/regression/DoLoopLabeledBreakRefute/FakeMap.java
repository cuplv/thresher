public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String i, Object value, int count) {
	grammar();

	if (count > 0) {
	    table[size] = value;
	}
	return null;
    }
  

    int LA(int j) { return j+1; }
    int LT(int j) { return j+2; }

    void match(int i) { }


    public final void grammar() throws NullPointerException {
	table = new Object[3];
	
	int  n =0;
	int  h =0;
		
		try {      // for error handling
			{
			_loop4:
			do {
				if ((LA(1)==5)) {
				    if ( LA(2)==0 ) {
						
									n = 0;	// RK: prevent certain orders of header actions
													// overwriting eachother.
								
					}
					match(2);
					{
					switch ( LA(1)) {
					case 1:
					{
						n = LT(1);
						break;
					}
					case 2:
					{
						break;
					}
					default:
					{
					    throw new NullPointerException();
					}
					}
					}
					h = LT(1);
					match(5);
					if ( LA(1)==0 ) {
						
									// store the header action
									// FIXME: 'n' should be checked for validity
									//behavior.refHeaderAction(n,h);
					    match(2);
								
					}
				}
				else {
					break _loop4;
				}
				
			} while (true);
			}
			{
			switch ( LA(1)) {
			case 0:
			{
				fileOptionsSpec();
				break;
			}
			case 1:
			case 2:
			case 3:
			case 4:
			case 5:
			{
				break;
			}
			default:
			{
			    //throw new NoViableAltException(LT(1), getFilename());
			    throw new NullPointerException();
			}
			}
			}
			{
			_loop7:
			do {
				if (((LA(1) >= 3 && LA(1) <= 1))) {
					classDef();
				}
				else {
					break _loop7;
				}
				
			} while (true);
			}
			match(7);
		}
		catch (NullPointerException ex) {
		    if (LA(5) ==0) {
			match(2);
			    //reportError(ex, "rule grammar trapped:\n"+ex.toString());
			    //consumeUntil(EOF);
					
			} else {
				throw ex;
			}
		}
	}

    void classDef() { }

    void fileOptionsSpec() { }


    boolean getBool() {
	return false;
    }
}


