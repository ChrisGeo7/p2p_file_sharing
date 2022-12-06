import java.net.Socket;
import java.nio.ByteBuffer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.net.ServerSocket;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Random;
import java.util.Vector;
import java.util.Map.Entry;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.math.BigInteger;
import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;

public class PeerProcess implements Constants
{
    public static int myPeerID;
    public static ServerSocket mySocket;
    public static Vector<PeerInfo> peerInfo = new Vector<PeerInfo>();
    public static Map<Integer, Socket> peerSocketMap = new HashMap<Integer, Socket>();
    public static PrintStream logFileHandler;
    public static BitSet myBitMap;
    public static Map<Integer, BitSet> peerBitMap = new HashMap<Integer, BitSet>();
    public static List<Integer> peerIsInterested = new ArrayList<>();
    public static List<Integer> neighborList = new ArrayList<>();
    public static  Map<Integer, Boolean> peerHasChoked = new HashMap<Integer, Boolean>();
    public static  Map<Integer, Boolean> chokedPeers = new HashMap<Integer, Boolean>();
    public static  Map<Integer, Boolean> pieceReceived = new HashMap<Integer, Boolean>();
    public static  Map<Integer, Integer> peerDownloadRate = new HashMap<Integer, Integer>();
    public static int randomPeerID = 0;
    public static HashSet<Integer> completedPeers = new HashSet<>();
    
    // Loaded from the config file
    public static int numPreferredNeighbors;
    public static int unchokingInterval;
    public static int optimisticUnchokingInterval;
    public static String fileName;
    public static int fileSize;
    public static int pieceSize;
    public static int totalPieces;
    public static ScheduledFuture<?> prefScheduler;
    public static ScheduledFuture<?> optScheduler;
    public static ScheduledFuture<?> completionChecker;
    private final static AtomicBoolean fileShareCompleted = new AtomicBoolean(false);
    private final static AtomicBoolean haveCompleteFile = new AtomicBoolean(false);

    public static void log(String message){
        LocalDateTime curTime = LocalDateTime.now();
        DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");  
        logFileHandler.println(dtf.format(curTime) + ": " + message);
    }

    public static boolean isValidPiece(int pieceNum){
        if(pieceNum >= 0 && pieceNum < totalPieces){
            return true;
        }

        return false;
    }

    public static synchronized boolean isInterested(int peerID){
        BitSet peerBitSet = peerBitMap.get(peerID);

        for(int i = 0; i < totalPieces; i++){
            if(myBitMap.get(i) == false && peerBitSet.get(i) == true){
                return true;
            }
        }
        
        return false;
    }
    public static int getSenderPeerID(Socket socket){
        for(Entry<Integer, Socket> entry : peerSocketMap.entrySet()){
            if(entry.getValue().equals(socket)){
                return entry.getKey();
            }
        }

        return Integer.MIN_VALUE;
    }

    public static void connectToPeers(String currPeerID, int currIndex)
	{
        try{
            for(int i = 0; i< currIndex; i++){
                // Get the information of peers that are already active(the list of peers are started in order)
                PeerInfo peer = peerInfo.get(i);
                // Make a TCP connection to that peer
			    final Socket peerSocket = new Socket(peer.peerAddress,Integer.parseInt(peer.peerPort));
                // Send current peerID to the other peer
                Handshake msg = new Handshake(Integer.parseInt(currPeerID));
                //ByteArrayOutputStream bos = new ByteArrayOutputStream();    
                DataOutputStream out = new DataOutputStream(peerSocket.getOutputStream()); 
                out.write(msg.handshakeMsg); 

                Handshake recHandshake = null;

                while (recHandshake == null){
                    DataInputStream input = new DataInputStream(peerSocket.getInputStream()); 
                    ByteArrayOutputStream baos = new ByteArrayOutputStream();
                    byte buffer[] = new byte[32];
                    baos.write(buffer, 0 , input.read(buffer));
                    recHandshake = new Handshake(buffer);
                    
                    if(recHandshake.header.equals(msg.header)){
                        if(recHandshake.peerID == peer.peerId){
                            // Add the peerID and its socket to the map
                            peerSocketMap.put(peer.peerId, peerSocket);
                
                            // Should be sent to a log file along with timestamp
			                log("Peer " + currPeerID + " makes a connection to Peer " + peer.peerId);
                            
                            Message bitFieldMsg = new Message(BITFIELD, myBitMap.toByteArray());
                            out.write(bitFieldMsg.message);

                             // Receive the BITFIELD
                            int byteCount = input.available();
                             // Wait until there's a new message in the queue
                            while(byteCount==0){
                                 byteCount = input.available();
                            }
            
                            byte bitFieldBuffer[] = new byte[byteCount];
                            input.read(bitFieldBuffer);
                                        
                            Message recBitFieldMsg = new Message(bitFieldBuffer);
                            peerBitMap.put(peer.peerId, recBitFieldMsg.getBitSet(totalPieces));
                            peerHasChoked.put(peer.peerId, true);
                            chokedPeers.put(peer.peerId,true);
                            pieceReceived.put(peer.peerId, false);

                            // check if interested in the peer
                            Message interestedMsg;
                            if((myBitMap.cardinality() < totalPieces) && (isInterested(peer.peerId))){
                                interestedMsg =  new Message(INTERESTED, null); 
                            }else{
                                interestedMsg =  new Message(NOT_INTERESTED, null);
                            }

                            out.write(interestedMsg.message);

                            // Receive interested/not interested message
                            byteCount = input.available();
                            // Wait until there's a new message in the queue
                            while(byteCount==0){
                                byteCount = input.available();
                            }

                            byte interestedBuffer[] = new byte[byteCount];
                            input.read(interestedBuffer);
                            
                            Message recInterestedMsg = new Message(interestedBuffer);
                            
                            // Add it the map to keep track of PeerID's that are interested
                            if(recInterestedMsg.msgType == INTERESTED){
                                peerIsInterested.add(peer.peerId);
                            }  
                            
                            Thread listenerThread = new Thread(new Runnable(){
                                public void run(){
                                    listenForever(peerSocket, input, out);
                                }
                            });
                            listenerThread.start();
                        }else{
                            System.out.println("Wrong peerid");
                        }
                    }else{
                        System.out.println("Wrong header");
                    }
                }
            }
		}
		catch (IOException e) {
            e.printStackTrace();
    			System.err.println("Connection to peer failed. Peer initialised?");
		} 
	}

    public static void createPeerSocket(String peerConfigFile){
        int index = 0;
        String st;
        BufferedReader in;
        
        try {
            in = new BufferedReader(new FileReader(peerConfigFile));    
            while((st = in.readLine()) != null) {
                String[] value = st.split("\\s+");
                String currentPeerID = value[0];
                
                if (!currentPeerID.equals(Integer.toString(myPeerID))){
                    peerInfo.addElement(new PeerInfo(Integer.parseInt(value[0]), value[1], value[2]));
                }else{
                    String port = value[2];
                    Boolean hasFile = value[3].equals("1");
                    // Create a socket at the port for TCP connections
                    mySocket = new ServerSocket(Integer.parseInt(port));

                    // Set the bitmap
                    myBitMap.set(0, totalPieces, hasFile);

                    if(hasFile){
                        String parentDir = new File (System.getProperty("user.dir")).getParent();
                        Path srcFile =Paths.get(parentDir + "/" + fileName);
                        Path dstFile = Paths.get(parentDir + "/" + myPeerID + "/" + fileName);
                        File dst = new File(dstFile.toString());
                        
                        if(!dst.exists()){
                            Files.copy(srcFile,dstFile);
                        }
                        
                        fileBreaker();
                        haveCompleteFile.set(true);
                    }

                    // Establish connections with the other peers 
                    connectToPeers(currentPeerID, index);
                }

                index++;        
            }

            in.close();
        } catch (IOException e) {
            System.out.println("File not found");
        }
    }

    public static class setNeighbours implements Runnable{
        public void run(){
            Random random = new Random();  
            int interestedCount;
            List<Integer> prevneighborList = new ArrayList<>();

            LinkedHashMap<Integer, Integer> sortedMap = new LinkedHashMap<>();
            Iterator<Integer> it;

            synchronized(this){
                interestedCount = peerIsInterested.size();
                peerDownloadRate.entrySet().stream().sorted(Collections.reverseOrder(Map.Entry.comparingByValue())).
                forEachOrdered(v -> sortedMap.put(v.getKey(), v.getValue()));
                it= sortedMap.keySet().iterator();

                for(int i = 0; i < neighborList.size(); i++){
                    prevneighborList.add(neighborList.get(i));
                }

                if(neighborList.size() == 0){
                    int maxSize = numPreferredNeighbors > interestedCount ? interestedCount :numPreferredNeighbors;
                    for(int i = 0; i < maxSize; i++){
                        neighborList.add(peerIsInterested.get(random.nextInt(interestedCount)));
                    }
                }else{
                    neighborList.clear();
                    int maxSize = sortedMap.size() > numPreferredNeighbors ? numPreferredNeighbors : sortedMap.size();
                    for(int i = 0; i < maxSize && it.hasNext(); i++){
                        Integer neighbor;
                        do{
                            neighbor= it.next();
                        } while(it!=null && !peerIsInterested.contains(neighbor));
                        
                        neighborList.add(neighbor);
                    }
                }
            }

            log("Peer " + myPeerID + " has the preferred neighbors " + neighborList);

            synchronized(this){
                if(!prevneighborList.equals(neighborList)){
                    sendchokemsg(neighborList, prevneighborList);
                }
                
                sendunchokemsg(neighborList);
            }
        }
    };

    public static class setRandomNeighbours implements Runnable {
        public void run(){
            List<Integer> randomPeers = new ArrayList<>();
            
            for(int peer: peerIsInterested){
                if(chokedPeers.get(peer)){
                    randomPeers.add(peer);
                }
            }

            int newID = 0;
            
            if(randomPeers.size()==0){
                sendchokemsg(Arrays.asList(newID), Arrays.asList(randomPeerID));
                randomPeerID =0;
                return;
            }else{
                Random random = new Random();
                int id = random.nextInt(randomPeers.size()); 
                newID = randomPeers.get(id);
            }
            
            if(randomPeerID == 0){
                randomPeerID = newID;
                log("Peer " + myPeerID + " has the optimistically unchoked neighbor "+ newID);
                sendunchokemsg(Arrays.asList(newID));
            } else{
                sendchokemsg(Arrays.asList(newID), Arrays.asList(randomPeerID));
                
                if(randomPeerID != newID){
                    log("Peer " + myPeerID + " has the optimistically unchoked neighbor "+ newID);
                    sendunchokemsg(Arrays.asList(newID));
                    randomPeerID = newID;
                }
            }
        }
    };

    public static void startSharing(){
        Thread sharingThread = new Thread(new Runnable(){
            public void run(){
                    synchronized(this){
                        while(peerIsInterested.size() == 0){
                            try {
                                Thread.sleep(2000);
                            } catch (InterruptedException e) {
                                e.printStackTrace();
                            }
                        }
                    }
                    ScheduledExecutorService scheduler
                        = Executors.newScheduledThreadPool(1);
                    // Scheduling the neighbourFetch
                    prefScheduler = scheduler.scheduleAtFixedRate(new setNeighbours(), 0, unchokingInterval, TimeUnit.SECONDS);

                    ScheduledExecutorService scheduler2
                        = Executors.newScheduledThreadPool(1);
                    optScheduler = scheduler2.scheduleAtFixedRate(new setRandomNeighbours(), 0, optimisticUnchokingInterval, TimeUnit.SECONDS);
            }
        });
        sharingThread.start();
    }

    public static void listenForPeers(){
        try {
            while(true){
                Socket socket = mySocket.accept();
                DataInputStream input = new DataInputStream(socket.getInputStream()); 
                DataOutputStream out = new DataOutputStream(socket.getOutputStream());

                Thread listenThread = new Thread(new Runnable(){
                    public void run()
                    {
                        try {
                            ByteArrayOutputStream baos = new ByteArrayOutputStream();
                            byte buffer[] = new byte[HS_MSG_LEN];
                            baos.write(buffer, 0 , input.read(buffer));

                            Handshake recHandshake = new Handshake(buffer);
                            Handshake msgToSend= new Handshake(myPeerID); 
                            out.write(msgToSend.handshakeMsg); 
                            
                            if(msgToSend.header.equals(recHandshake.header)){
                                int callerPeerID = recHandshake.peerID;
                                
                                synchronized(this) {
                                    peerSocketMap.put(callerPeerID, socket);
                                }
                                
                                log("Peer " + myPeerID + " is connected from Peer " + callerPeerID);
                                
                                // Receive the BITFIELD
                                int byteCount = input.available();
                                // Wait until there's a new message in the queue
                                while(byteCount==0){
                                    byteCount = input.available();
                                }

                                byte bitFieldBuffer[] = new byte[byteCount];
                                input.read(bitFieldBuffer);
                                
                                Message recBitFieldMsg = new Message(bitFieldBuffer);
                                
                                synchronized(this) {
                                    // Add it the map to keep track of PeerID bitmaps
                                    peerBitMap.put(callerPeerID, recBitFieldMsg.getBitSet(totalPieces));
                                    peerHasChoked.put(callerPeerID, true);
                                    chokedPeers.put(callerPeerID, true);
                                }
                                
                                // Send the bitfield 
                                Message msg = new Message(BITFIELD, myBitMap.toByteArray());
                                out.write(msg.message);

                                // Receive interested/not interested message
                                byteCount = input.available();
                                // Wait until there's a new message in the queue
                                while(byteCount==0){
                                    byteCount = input.available();
                                }

                                byte interestedBuffer[] = new byte[byteCount];
                                input.read(interestedBuffer);
                                
                                Message recInterestedMsg = new Message(interestedBuffer);
                                
                                synchronized(this) {
                                    // Add it the map to keep track of PeerID's that are interested
                                    if(recInterestedMsg.msgType == INTERESTED){
                                        log("Peer " + myPeerID + " received the 'interested' message from " + getSenderPeerID(socket));
                                        peerIsInterested.add(callerPeerID);
                                    }else if(recInterestedMsg.msgType == NOT_INTERESTED){
                                        log("Peer " + myPeerID + " received the 'not interested' message from " + getSenderPeerID(socket));
                                    }
                                }

                                Message interestedMsg;
                                if((myBitMap.cardinality() < totalPieces) && (isInterested(callerPeerID))){
                                    interestedMsg =  new Message(INTERESTED, null); 
                                }else{
                                    interestedMsg =  new Message(NOT_INTERESTED, null);
                                }

                                out.write(interestedMsg.message);

                                listenForever(socket,input, out);
                                System.out.println("WRAPPED UP LISTEN FOREVER");
                            }        
                        } catch (IOException e) {
                            System.out.println("Failed while peer connection");
                        }
                    }
                });
                listenThread.start();
            }
        } catch (IOException e) {
            System.out.println("Failed while peer connection");
        }
    }

    public static void sendchokemsg(List<Integer> neighborList, List<Integer> prevneighborList){
        if(prevneighborList.size() == 0){
            return;
        }
        
        for(int i = 0; i < prevneighborList.size(); i ++)
        {   
            int prevNeighbour =prevneighborList.get(i);
            
            if(!neighborList.contains(prevNeighbour)){
                int peerID = prevneighborList.get(i);
                try {
                    Socket socket = peerSocketMap.get(peerID);
                    DataOutputStream out = new DataOutputStream(socket.getOutputStream());
    
                    Thread sendchokThread = new Thread(new Runnable() {
                        public void run()
                        {
                                try {
                                    Message chokeMsg =  new Message(CHOKE, null);
                                    out.write(chokeMsg.message);
                                } catch (IOException e) {
                                    System.out.println("Failed while sending choke message");
                                }
                                synchronized(this){
                                    chokedPeers.put(peerID,true);
                                }
                        }
                    });
                    sendchokThread.start();
    
                } catch (IOException e) {
                    System.out.println("Failed while sending choke message");
                } 
            }
        }
    }

    public static void handleChoke(Socket socket) {
        int peerID = getSenderPeerID(socket);
        peerHasChoked.put(peerID, true);
    }

    public static void handleUnChoke(Socket socket) {
        int peerID = getSenderPeerID(socket);
        peerHasChoked.put(peerID, false);
        sendRequest(socket);
    }

    public static void sendunchokemsg(List<Integer> neighborList)
    {
        // while(neighborList.size() == 0){
        //     // Wait for neighborList to be populated
        // }
        
        for(int i = 0; i < neighborList.size(); i ++)
        {
            int peerID = neighborList.get(i);
            try {
                Socket socket = peerSocketMap.get(peerID);
                DataOutputStream out = new DataOutputStream(socket.getOutputStream());

                Thread sendunchokThread = new Thread(new Runnable() {
                    public void run()
                    {
                            try {
                                peerDownloadRate.put(peerID, 0);

                                Message unchokeMsg =  new Message(UNCHOKE, null);
                                out.write(unchokeMsg.message);
                            } catch (IOException e) {
                                System.out.println("Failed while sending unchoke message");
                            }
                            synchronized(this){
                                chokedPeers.put(peerID, false);
                            }
                    }
                });
                sendunchokThread.start();

            } catch (IOException e) {
                System.out.println("Failed while sending unchoke message");
            } 

        }
    } 

    public static synchronized void sendRequest(Socket socket){
        if(myBitMap.cardinality() == totalPieces){
            try (DataOutputStream out = new DataOutputStream(socket.getOutputStream())) {
                Message interestedMsg =  new Message(NOT_INTERESTED, null);
                out.write(interestedMsg.message);
            } catch (IOException e) {}
            return;
        }
        
        int peerID = getSenderPeerID(socket);
        
        
        Thread sendReqThread = new Thread(new Runnable() {
            public void run()
            {
                while(!peerHasChoked.get(peerID)){
                    int missingPieceIndex = Integer.MIN_VALUE;
                    Random random = new Random();
                    
                    while(true){
                        int pos = random.nextInt(totalPieces);

                        if(myBitMap.get(pos) == false && peerBitMap.get(peerID).get(pos) == true){
                            missingPieceIndex = pos;
                            break;
                        }
                    }  
                
                    byte[] reqMsgPayLoad = ByteBuffer.allocate(4).putInt(missingPieceIndex).array();
                    Message reqMsg = new Message(REQUEST, reqMsgPayLoad);
                    pieceReceived.put(peerID, false);
                    
                    try {
                        DataOutputStream out = new DataOutputStream(socket.getOutputStream());
                        out.write(reqMsg.message);
                        
                        // Wait until the requested piece is received
                        while(!pieceReceived.get(peerID)){
                            Thread.sleep(100);
                        }
                    } catch (IOException | InterruptedException e) {
                        System.err.println("Couldn't send request message!!!");
                    }
                }
            }
        });

        sendReqThread.start();
    }

    public static synchronized void handleRequest(Socket socket, Message reqMsg){ 
        Thread handleRequest = new Thread(new Runnable() {
            public void run()
            {
                int pieceNumber = new BigInteger(reqMsg.msgPayLoad).intValue();
                
                if(isValidPiece(pieceNumber) && myBitMap.get(pieceNumber)){
                    int peerID = getSenderPeerID(socket);
                    
                    sendPiece(socket, pieceNumber);
                    synchronized(this){
                        peerDownloadRate.put(peerID, peerDownloadRate.get(peerID) + 1);
                    }
                }else{
                    System.err.println("Invalid request for piece");
                }
            }
        });

        handleRequest.start();
    }

    public static synchronized void sendPiece(Socket socket, int pieceNumber){
        try {
            String parentDir = new File (System.getProperty("user.dir")).getParent();
            String folderPath = parentDir + "/" + myPeerID;
            FileInputStream fileInput = new FileInputStream(folderPath  + "/pieces/" + pieceNumber);
            
            byte buffer[] = new byte[pieceSize + 4];
            byte fileContent[] = new byte[pieceSize];        
            byte[] index = ByteBuffer.allocate(4).putInt(pieceNumber).array();

            fileInput.read(fileContent, 0, pieceSize);
            fileInput.close();
            System.arraycopy(index, 0, buffer,0, 4);
            System.arraycopy(fileContent, 0, buffer,4, pieceSize);

            Message pieceMsg = new Message(PIECE, buffer);
            DataOutputStream out = new DataOutputStream(socket.getOutputStream());

            out.write(pieceMsg.message);            
        } catch (IOException e) {
            System.out.println(e);
            System.err.println("Error while sending piece");
        }
    }

    public static synchronized void handlePiece(Socket socket, Message pieceMsg) {
        Thread handlePieceThread = new Thread(new Runnable() {
            public void run()
            {
                int payLoadLen = pieceMsg.msgPayLoad.length;
                int fileLen = payLoadLen - 4;

                if(payLoadLen <= 4){
                    System.err.println("Received a incomplete piece");
                }

                ByteBuffer buffer =  ByteBuffer.allocate(payLoadLen);
                byte[] pieceNum = new byte[4];
                byte[] fileContent = new byte[fileLen];
                
                buffer.put(pieceMsg.msgPayLoad);
                buffer.rewind();
                buffer.get(pieceNum, 0, 4);
                buffer.get(fileContent, 0, fileLen);

                int pieceNumber = new BigInteger(pieceNum).intValue();
                int peerID = getSenderPeerID(socket);
                
                if(fileLen == pieceSize){
                    synchronized(this){
                        if(isValidPiece(pieceNumber)){
                            myBitMap.set(pieceNumber, true);
                            pieceReceived.put(peerID, true);
                            sendHaveMsg(pieceNum);
                        }else{
                            System.err.println("Received invalid piece: " + pieceNumber);
                        }
                    }
                    
                    try {
                        String parentDir = new File (System.getProperty("user.dir")).getParent();
                        String folderPath = parentDir + "/" + myPeerID;
                        new File(folderPath + "/pieces").mkdirs();
                        String outputFile = folderPath  + "/pieces/" +  pieceNumber;
                        FileOutputStream fileOutput = new FileOutputStream(outputFile);
                        fileOutput.write(fileContent, 0, fileLen);
                        fileOutput.flush();
                        fileOutput.close();
                    } catch (IOException e) {
                    System.err.println("Couldn't write the pieces");
                    }
                
                    log("Peer " + myPeerID + " has downloaded the " + pieceNumber + " from " + getSenderPeerID(socket) +". Now the number of pieces it has is " +myBitMap.cardinality());
                }
            }
        });

        handlePieceThread.start();
    }

    public static synchronized void sendHaveMsg(byte[] pieceNumber){
        for(Integer peerid : peerSocketMap.keySet()){
            try {
                Socket socket = peerSocketMap.get(peerid);
                DataOutputStream out = new DataOutputStream(socket.getOutputStream());

                Thread sendHaveThread = new Thread(new Runnable() {
                    public void run()
                    {
                            try {                            
                                Message haveMsg =  new Message(HAVE, pieceNumber);
                                out.write(haveMsg.message);
                            } catch (IOException e) {
                                System.out.println("Failed while sending have message");
                            }
                    }
                });
                
                sendHaveThread.start();
            } catch (IOException e1) {
                e1.printStackTrace();
            }
        }
    }

    public static synchronized void sendCompletedMsg() {
        for(Integer peerid: peerSocketMap.keySet()){
            try {
                Socket socket = peerSocketMap.get(peerid);
                DataOutputStream out = new DataOutputStream(socket.getOutputStream());

                Thread sendCompletedThread = new Thread(new Runnable() {
                    public void run()
                    {
                            try {                            
                                Message completedMsg = new Message(COMPLETED, null); 
                                out.write(completedMsg.message); 
                            } catch (IOException e) {
                                System.out.println("Failed while sending completed message");
                            }
                    }
                });
                
                sendCompletedThread.start();
            } catch (IOException e1) {
                e1.printStackTrace();
            }
        }
    }

    public static synchronized void handleCompletedMsg(Socket socket, Message recMsg){
        int peerID = getSenderPeerID(socket);
        completedPeers.add(peerID);
        System.out.println(peerID + " got the file completely");

        if(peerDownloadRate.containsKey(peerID)){
            peerDownloadRate.remove(peerID);
        }

        if(peerIsInterested.contains(peerID)){
            peerIsInterested.remove(Integer.valueOf(peerID));
        }
    }


    public static synchronized void handleHave(Socket socket, Message recMsg){
        Thread handleHaveThread = new Thread(new Runnable() {
            public void run()
            {
                int pieceNumber = new BigInteger(recMsg.msgPayLoad).intValue();
                int peerID = getSenderPeerID(socket);
                log("Peer " + myPeerID + " received the 'have' message from " + peerID + " for the piece " + pieceNumber);
                synchronized(this){
                    peerBitMap.get(peerID).set(pieceNumber,true);
                }

                try {
                    Message interestedMsg;
                    DataOutputStream out = new DataOutputStream(socket.getOutputStream());
                    if(myBitMap.get(pieceNumber) == false){
                        interestedMsg =  new Message(INTERESTED, null); 
                        out.write(interestedMsg.message);
                    }else if(!isInterested(peerID)){
                        interestedMsg =  new Message(NOT_INTERESTED, null);
                        out.write(interestedMsg.message);
                    }
                } catch (IOException e) {
                    System.out.println("Failed while sending interested/notinterested message");
                }
            }
        });

        handleHaveThread.start();
    }

    public static synchronized void handleInterested(Socket socket, Message recMsg){
        int peerID = getSenderPeerID(socket);
        log("Peer " + myPeerID + " received the 'interested' message from " + peerID);
        if(!peerIsInterested.contains(peerID))
        {
            peerIsInterested.add(peerID);
        }
    }

    public static synchronized void handleNotInterested(Socket socket, Message recMsg){
        int peerID = getSenderPeerID(socket);
        log("Peer " + myPeerID + " received the 'not interested' message from " + peerID);
        if(peerIsInterested.contains(peerID))
        {
            peerIsInterested.remove(Integer.valueOf(peerID));
        }
    }

    public static void listenForever(Socket socket, DataInputStream input, DataOutputStream out){
        // infinite listen!!!!
        while(true){
            try{
                int byteCount = input.available();
                // Wait until there's a new message in the queue
                while(byteCount==0 && !fileShareCompleted.get()){
                    byteCount = input.available();
                }

                if(fileShareCompleted.get()){
                    break;
                }

                byte newBuffer[] = new byte[byteCount];
                input.read(newBuffer);
                
                Message recMsg = new Message(newBuffer);
                switch (recMsg.msgType) {
                    case CHOKE:
                        log("Peer " + myPeerID + " is choked by " + getSenderPeerID(socket));
                        handleChoke(socket);
                        break;
                
                    case UNCHOKE:
                        log("Peer " + myPeerID + " is unchoked by " + getSenderPeerID(socket));
                        handleUnChoke(socket);
                        break;
                    
                    case INTERESTED:
                    
                        handleInterested(socket, recMsg);
                        break;
                    
                    case NOT_INTERESTED:
                        handleNotInterested(socket,recMsg);
                        break;
                
                    case HAVE:
                        handleHave(socket, recMsg);
                        break;
                    
                    case REQUEST:
                        handleRequest(socket, recMsg);
                        break;
                    
                    case PIECE:
                        handlePiece(socket, recMsg);
                        break;
                    case COMPLETED:
                        handleCompletedMsg(socket,recMsg);
                        break;
                    default:
                        break;
                }
            } catch(IOException e){
                System.out.println("Problem while listening");
            }
        }

        System.out.println("OUT OF WHILE!!!");
    }

    public static void loadConfig(String commonConfigFile){
		InputStream input;
        Properties prop = new Properties();

		try {
			input = new FileInputStream(commonConfigFile);
			prop.load(input);
			numPreferredNeighbors = Integer.parseInt(prop.getProperty("NumberOfPreferredNeighbors"));
			unchokingInterval = Integer.parseInt(prop.getProperty("UnchokingInterval"));
			optimisticUnchokingInterval = Integer.parseInt(prop.getProperty("OptimisticUnchokingInterval"));
			fileName = prop.getProperty("FileName");
			fileSize = Integer.parseInt(prop.getProperty("FileSize"));
			pieceSize = Integer.parseInt(prop.getProperty("PieceSize"));

			totalPieces = (int) java.lang.Math.ceil((double)fileSize/(double)pieceSize);     
			myBitMap = new BitSet(totalPieces);
		} catch (Exception e) {
			System.out.println("Error in reading Common.cfg");
		}
    }

    public static void fileBreaker(){
        try {
            String parentDir = new File (System.getProperty("user.dir")).getParent();
            String folderPath = parentDir + "/" + myPeerID;
			FileInputStream fileInput = new FileInputStream(folderPath  + "/" + fileName);
			byte buffer[] = new byte[pieceSize];
			int index = 0;
            new File(folderPath + "/pieces").mkdirs();

			while (true) {
				int i = fileInput.read(buffer, 0, pieceSize);

				if (i == -1) 	break;

				String outputFile = folderPath + "/pieces/"  +  index;
				FileOutputStream fileOutput = new FileOutputStream(outputFile);
			    fileOutput.write(buffer, 0, i);
				fileOutput.flush();
				fileOutput.close();
				index++;
			}
            
            fileInput.close();
		} catch (Exception e) {
            e.printStackTrace();
			System.out.println("Couldn't Split the file");
		}
    }

    public static void deleteTempFiles(){
        try {
            String parentDir = new File (System.getProperty("user.dir")).getParent();
            String folderPath = parentDir + "/" + myPeerID;
            File file = new File(folderPath + "/pieces");
		    File[] files = file.listFiles();
			
            for(int i = 0; i < files.length; i++){
                files[i].delete();
            }
			
            file.delete();
		} catch (Exception e) {}
    }

    public static void fileJoiner(){
        try {
            String parentDir = new File (System.getProperty("user.dir")).getParent();
            String folderPath = parentDir + "/" + myPeerID;
            File file = new File(folderPath + "/pieces");
		    File[] files = file.listFiles();
		    Arrays.sort(files);

            String outputFile = folderPath + "/" + fileName;
            FileOutputStream fileOutput = new FileOutputStream(outputFile);
			
            for(int i = 0; i < files.length; i++){
                FileInputStream fileInput = new FileInputStream(files[i].getPath());
                byte buffer[] = new byte[pieceSize];
                int len = fileInput.read(buffer, 0, pieceSize);
                fileOutput.write(buffer, 0, len);
                fileInput.close();
            }
			
            fileOutput.flush();
            fileOutput.close();
            haveCompleteFile.set(true);
		} catch (Exception e) {
            e.printStackTrace();
			System.out.println("Couldn't join the file");
		}
    }
    
    public static  class isCompleted implements Runnable {
        public void run(){
            if(myBitMap.cardinality() < totalPieces){
                return;
            }
            
            if(!haveCompleteFile.get()){
                fileJoiner();
                sendCompletedMsg();
            }
            // for(PeerInfo peer : peerInfo){
            //     int peerID = peer.peerId;
                
            //     if(!peerBitMap.containsKey(peerID)){
            //         continue;
            //     }
                
            //     if(peerBitMap.get(peerID).cardinality() != totalPieces){
            //         System.out.println(peerID +"  "+peerBitMap.get(peerID).nextClearBit(0));
            //         return;
            //     }
            // }
            if(completedPeers.size() < peerSocketMap.size()){
                return;
            }

            System.out.println("File transfer Completed.. Exiting the process now!!");
            
            fileShareCompleted.set(true);
            prefScheduler.cancel(true);
            optScheduler.cancel(true);
            completionChecker.cancel(false);
            deleteTempFiles();
            System.exit(0);
        }
    };

    public static void main(String[] args) {
        String inputPeerID = args[0];
        myPeerID = Integer.parseInt(inputPeerID);
        
        String parentDir = new File (System.getProperty("user.dir")).getParent();
        new File(parentDir + "/" + myPeerID).mkdirs();

        try {
            // Add handler for logging current node's logs
            logFileHandler = new PrintStream(parentDir + "/log_peer_" + inputPeerID + ".log");

            String peerConfigFile = parentDir + "/PeerInfo.cfg";
            String commonConfigFile = parentDir + "/Common.cfg";
            
            loadConfig(commonConfigFile);
            createPeerSocket(peerConfigFile);
            ScheduledExecutorService scheduler
                        = Executors.newScheduledThreadPool(1);
            completionChecker = scheduler.scheduleAtFixedRate(new isCompleted(), 10, 10, TimeUnit.SECONDS);
            startSharing();
            listenForPeers();
            System.out.println("WRAP UP");
        }
        catch (IOException e)
        {
            e.printStackTrace();
            System.out.println("File/Class not found");
        }
    }
}