import java.io.Serializable;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.util.BitSet;


public class Message implements Serializable, Constants {
    public byte[] message;
    public int msgLen;
    public int msgType;
    public byte[] msgPayLoad;

    Message(int msgType, byte[] msgPayLoad){
        int payLoadLen = (msgPayLoad != null) ? msgPayLoad.length :0;
        int payLoadOffset = MSG_LEN_FIELD_LEN + MSG_TYPE_LEN;
        int totalLen = payLoadOffset + payLoadLen;

        this.msgType= msgType;
        this.msgPayLoad=new byte[payLoadLen];
        this.msgPayLoad= msgPayLoad;

        if(msgType == CHOKE || msgType == UNCHOKE || msgType == INTERESTED || msgType == NOT_INTERESTED || msgType == COMPLETED){
            this.msgLen = MSG_TYPE_LEN;
        }else if(msgType == HAVE || msgType == REQUEST || msgType == PIECE){
            this.msgLen = MSG_TYPE_LEN + 4;
        }else if(msgType == BITFIELD){
            this.msgLen = MSG_TYPE_LEN + payLoadLen;
        }

        message = new byte[totalLen];

        byte[] msgLenByteArr = ByteBuffer.allocate(MSG_LEN_FIELD_LEN).putInt(msgLen).array();

        for(int i = 0; i < MSG_LEN_FIELD_LEN; i++){
            message[i] = msgLenByteArr[i];
        }
        
        message[MSG_LEN_FIELD_LEN] = (byte) msgType;

        for(int i = 0; i < payLoadLen; i++){
            message[payLoadOffset + i] = msgPayLoad[i];
        }
    }

    Message(byte[] message){
        int totalLen = message.length;
        int payLoadOffset = MSG_LEN_FIELD_LEN + MSG_TYPE_LEN;
        
        ByteBuffer buffer =  ByteBuffer.allocate(totalLen);
        buffer.put(message);
        byte [] msgLen = new byte[MSG_LEN_FIELD_LEN];
        byte [] msgType = new byte[MSG_TYPE_LEN];
        byte [] msgPayLoad = new byte[totalLen - payLoadOffset];

  
        buffer.rewind();
        buffer.get(msgLen, 0, MSG_LEN_FIELD_LEN);
        buffer.get(msgType, 0, MSG_TYPE_LEN);
        
        if(totalLen > payLoadOffset){
            buffer.get(msgPayLoad, 0 , totalLen -  payLoadOffset);
        }   

        this.msgLen = new BigInteger(msgLen).intValue();
        this.msgType = new BigInteger(msgType).intValue();
        this.msgPayLoad = msgPayLoad;
        this.message = message;
    }

    public BitSet getBitSet(int totalPieces){
        if(this.msgLen <= 1){
            return new BitSet(totalPieces);
        }else{
            return BitSet.valueOf(this.msgPayLoad);
        }
    }
}
