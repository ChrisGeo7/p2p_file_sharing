public interface Constants {
	// For Handshake messages
	public static final int HS_MSG_LEN = 32;
	public static final int HS_HEADER_LEN = 18;
	public static final int HS_ZEROBITS_LEN = 10;
	public static final int HS_PEERID_LEN = 4;
	
	// For messages
	public static final int MSG_LEN_FIELD_LEN = 4;
	public static final int MSG_TYPE_LEN = 1;
	// public static final int DATA_MESSAGE_PAYLOAD is variable size
	
	// For message type 
	public static final int CHOKE = 0;
	public static final int UNCHOKE = 1;
	public static final int INTERESTED = 2;
	public static final int NOT_INTERESTED = 3;
	public static final int HAVE = 4;
	public static final int BITFIELD = 5;
	public static final int REQUEST = 6;
	public static final int PIECE = 7;
	public static final int COMPLETED = 8;
	
	// For 'have' messages
	public static final int PIECE_INDEX_FIELD = 4;
}