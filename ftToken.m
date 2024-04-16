
-- Fault-tolerant token coherence protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  QMax: 2;
  NetMax: ProcCount+1; -- TODO: needs to be a function of MaxPerfMsgs?
  MaxPerfMsgs: 2; -- Number of repeated perf reqs sent before persistent req
  MaxTokenSerialNum: 3;
  MaxSharerTokens: (ProcCount-1);
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
    Proc: scalarset(ProcCount);   -- unordered range of processors
    Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
    Token: scalarset(ProcCount); -- tokens
    Home: enum {HomeType};      -- need enumeration for IsMember calls
    Node: union {Home, Proc};

    SharerTokenCount: 0..(ProcCount-1);
    PerfMsgCount: 0..MaxPerfMsgs;
    SerialNumType: 0..MaxTokenSerialNum;

    MessageType: enum {
          GetS
        , GetM
        , IncSerialNum             -- (TRNet)
        , BackupInv                -- (TRNet)
        , DestructionDone          -- (TRNet) check data field to indicate DestructionDone with data
        , ActivatePersistent
        , DeactivatePersistent
        , PingPersistent           -- consequence of lost persistent deactivate timeout
        , AckO                     -- owner acknowledgement
        , AckBD                    -- backup deletion acknowledgement
        , StartTokenRec            -- (TRNet) start token recreation (only home can receive)
        , Tokens                   -- token transfer message type
        , IncSerialNumAck
    };

    
    Message:
        Record
            mtype: MessageType;
            src: Node;
            val: Value;
            numSharerTokens: SharerTokenCount;
            hasOwnerToken: boolean;
            serialNum: SerialNumType;
        End;

    HomeState:
        Record
            state: enum {
                -- TBD: Fill this
                -- TODO: Do we need a backup state? A potential optimization is getting rid of the MainMem backup state and having if no backup
                -- /owner token exists, then MainMem must have the most recent copy of data
                -- TODO: Is a recreating token state (R) necessary for MainMem?
                I   -- MainMem does not have any tokens
              , B   -- NOTE: Have this state for now
              , S   -- MainMem has one or more sharer tokens
              , Ob
              , O   -- MainMem has the owner token and, potentially, other sharer tokens
              , Mb
              , M   -- MainMem has every token
            };
            val: Value;
            numSharerTokens: SharerTokenCount;
            hasOwnerToken: boolean;
            hasBackupToken: boolean;
        End;

    ProcState:
        Record
            val: Value;
            numSharerTokens: SharerTokenCount;
            hasOwnerToken: boolean;
            hasBackupToken: boolean;
            req: MessageType;   -- Each proc needs to keep track of what request it is currently waiting a response for so re-issued requests can happen
            curSerial: SerialNumType;
            curPersistentRequester: Proc;
            persistentTable: array [Proc] of boolean;
            -- TODO: How should we add a persistent request table in Murphi?
            -- TODO: We also need to add a serial number table per cache
        End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
    MainMem:  HomeState;
    Procs: array [Proc] of ProcState;
    FaultNet: array [Node] of multiset [NetMax] of Message;  -- Performance and persistent messages, can be deleted
    TrNet: array [Node] of Message; -- Token recreation messages, cosmic ray proof, never deleted
    LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware


----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure BroadcastFaultMsg (
    mtype: MessageType;
    dst: Node;
    src: Node;
    val: Value;
    numSharerTokens: TokenCount;
    hasOwnerToken: boolean;
    serialId: SerialType;
);
var msg: Message;
Begin
    assert(!IsTRMsg(msg));
    assert(hasOwnerToken -> !isundefined(val)) "Data Transfer Rule violated";
    assert(hasOwnerToken -> Procs[src].hasBackupToken) "Blocked Ownership Rule violated";
    
    msg.mtype           := mtype;
    msg.dst             := dst;
    msg.src             := src;
    msg.val             := val;
    msg.numSharerTokens := numSharerTokens;
    msg.hasOwnerToken   := hasOwnerToken;
    msg.serialId        := serialId;

    -- Iterate through each node's multiset in faultnet and add the message
    Forall node : FaultNet Do
      assert(MultiSetCount(i: FaultNet[node], true) < NetMax) "Too many messages";
      MultiSetAdd(msg, FaultNet[node]);
    End;
End;

Procedure SendTRMsg (
    mtype: MessageType;
    dst: Node;
    src: Node;
    val: Value;
);
var msg: Message;
Begin
  assert(IsTRMsg(msg));

  msg.mtype   := mtype;
  msg.dst     := dst;
  msg.src     := src;
  msg.val     := val;

  TrNet[dst] := msg;
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
    error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
    error "Unhandled state!";
End;


Procedure ReceiveTokens(n:Node, msg:Message);
Begin
    alias p : Procs[n] do

    assert(msg.mtype = Tokens);

    -- Receive tokens
    if p.curSerial = msg.serialNum
    then
      assert(!isundefined(msg.numSharerTokens));
      p.numSharerTokens := p.numSharerTokens + msg.numSharerTokens;

      if msg.hasOwnerToken
      then
        assert(!isundefined(msg.val));
        assert(isundefined(p.hasOwnerToken));
        p.hasOwnerToken := true;
        p.val := msg.val;
        BroadcastFaultMsg(AckO, msg.src, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
      endif;
    endif;
    
    endalias; -- p
End;

Procedure PersistentTableActivate(rqstr:Proc)
Begin
  alias p : Procs[rqstr] Do

  p.persistentTable[rqstr] := true;

  if isundefined(p.curPersistentRequester) | rqstr < p.curPersistentRequester
  then
    p.curPersistentRequester := rqstr;
  end;

  endalias; -- p
End;

Procedure PersistentTableDeactivate(rqstr:Proc)
Begin
  alias p : Procs[rqstr] Do

  p.persistentTable[rqstr] := false;
  undefine p.curPersistentRequester;

  Forall n : Proc Do
    if p.persistentTable[n] = true & IsUndefined(p.curPersistentRequester) then
      p.curPersistentRequester := n;
    endif;
  End;
  
  endalias; -- p
End;

Procedure SendAllTokens(dst:Node, src:Node)
Begin
  alias p: Node[src] do

  if p.hasOwnerToken & p.hasBackupToken
  then
    BroadcastFaultMsg(Tokens, dst, src, p.val, p.numSharerTokens, true, p.curSerial);
    p.numSharerTokens := 0;
    p.hasOwnerToken := false;
  else
    BroadcastFaultMsg(Tokens, dst, src, UNDEFINED, p.numSharerTokens, false, p.curSerial);
    p.numSharerTokens := 0;
    undefine p.val;
  endif;

  endalias; -- p
End;

Function IsEntry(p:Proc)
Begin
  return p.persistentTable[p];
End;

Function HasTRMsg(n:Node) : boolean;
Begin
  return !isundefined(TrNet[n]);
End;

Function IsTRMsg(msg:Message) : boolean;
Begin
  return (msg.mtype = IncSerialNum |
          msg.mtype = BackupInv | 
          msg.mtype = DestructionDone | 
          msg.mtype = StartTokenRec);
End;

Procedure HomeReceive(msg:Message);
Begin
 alias h : MainMem do
    -- Debug output may be helpful:
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put MainMem.state;

    -- default to 'processing' message.  set to false otherwise
    switch msg.mtype
      case GetS:    -- README: In TokenB, which FtTokenCMP is based on, procs in S ignore transient read reqs
      -- (contd.) and the proc in O sends the data + 1 token on read request. Migratory sharing optimization is present
        if h.hasOwnerToken & h.hasBackupToken
        then
          BroadcastFaultMsg(Tokens, msg.src, h, h.val, h.numSharerTokens, true, h.curSerial);
          h.hasOwnerToken := false;
          h.numSharerTokens := 0;
        else
          if h.numSharerTokens > 0
          then
            BroadcastFaultMsg(Tokens, msg.src, h, h.val, h.numSharerTokens, false, h.curSerial);
            h.numSharerTokens := 0;
          endif;
        endif;

      case GetM:
        SendAllTokens(msg.src, h);

      case SetSerialNum:
        h.curSerial := msg.serialId;
        if h.hasOwnerToken then
          SendTRMsg(IncSerialNumAck, MainMem, h, h.val);
          h.numSharerTokens := 0;
          h.hasOwnerToken := false;
        else
          SendTRMsg(IncSerialNumAck, MainMem, h, UNDEFINED);
          h.numSharerTokens := 0;
        endif;
      
      case BackupInv:
        if h.hasBackupToken
        then
          h.hasBackupToken := false;
          undefine h.val;
        endif;

      case DestructionDone:        
        
        if !IsUndefined(msg.val) -- Destruction done w/ data
        then
          h.val := msg.val;
        endif;

        assert(!isundefined(h.val));
        h.numSharerTokens := MaxSharerTokens;
        h.hasOwnerToken := true;
        h.hasBackupToken := true;

      case ActivatePersistent:
        PersistentTableActivate(msg.src);
        -- Memory can never be the persistent requester
        SendAllTokens(h.curPersistentRequester, h);

      case DeactivatePersistent:
        -- TODO: Remove persistent request table entry
        PersistentTableDeactivate(msg.src);

      case PingPersistent:
        -- Shouldn't ever get pinged

      case AckO:
        if h.hasBackupToken & !h.hasOwnerToken then    -- Must be in Backup state
          BroadcastFaultMsg(AckBD, msg.src, h, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
          h.hasBackupToken := false;
          undefine h.val;
        endif;

      case AckBD:
        if !h.hasBackupToken & h.hasOwnerToken then    -- In blocked ownership state
          h.hasBackupToken := true;
        endif;

      case Tokens:
        ReceiveTokens(h, msg);
    endswitch;
End;


Procedure ProcReceive(msg: Message; n: Proc);
Begin
    put "Receiving "; put msg.mtype; put " at proc "; put p; put "\n";

    alias p: Procs[n] do

    -- Note: (dst == undefined) -> broadcast
    -- If we are not the intended dst, do nothing
    if !isundefined(msg.dst) & msg.dst != n
    then
      return;
    endif;

    switch msg.mtype

      case GetS:    -- README: In TokenB, which FtTokenCMP is based on, procs in S ignore transient read reqs
      -- (contd.) and the proc in O sends the data + 1 token on read request. Migratory sharing optimization is present
        if p.hasOwnerToken & p.hasBackupToken
        then
          BroadcastFaultMsg(Tokens, msg.src, p, p.val, p.numSharerTokens, true, p.curSerial);
          p.hasOwnerToken := false;
          p.numSharerTokens := 0;
        else
          if p.numSharerTokens > 0
          then
            BroadcastFaultMsg(Tokens, msg.src, p, p.val, p.numSharerTokens, false, p.curSerial);
            p.numSharerTokens := 0;
          endif;
        endif;

      case GetM:
        SendAllTokens(msg.src, p);

      case SetSerialNum:
        -- TODO: What are we using the serial numbers in our Proc Record for at the moment? Is it for bounded faults or does it
        -- (contd.) symbolize the token serial numbers?
        p.curSerial := msg.serialId;
        if p.hasOwnerToken then
          SendTRMsg(IncSerialNumAck, MainMem, p, p.val);
          p.numSharerTokens := 0;
          p.hasOwnerToken := false;
        else
          SendTRMsg(IncSerialNumAck, MainMem, p, UNDEFINED);
          p.numSharerTokens := 0;
        endif;
      
      case BackupInv:
        if p.hasBackupToken
        then
          p.hasBackupToken := false;
          undefine p.val;
        endif;

      case DestructionDone:        
        
        if !IsUndefined(msg.val) -- Destruction done w/ data
        then
          p.val := msg.val;
        endif;

        assert(!isundefined(p.val));
        p.numSharerTokens := MaxSharerTokens;
        p.hasOwnerToken := true;
        p.hasBackupToken := true;
        -- else
          -- TODO: restart timeouts
        -- endif;

      case ActivatePersistent:
        PersistentTableActivate(msg.src);
        -- if I am not the persistent requester, send all tokens
        if p != p.curPersistentRequester
        then
          SendAllTokens(p.curPersistentRequester, p);
        endif;

      case DeactivatePersistent:
        PersistentTableDeactivate(msg.src);

      case PingPersistent:
        if !IsEntry(p) then
         BroadcastFaultMsg(DeactivatePersistent, UNDEFINED, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED); -- TODO: I currently have msg.dst as UNDEFINED as this message is meant for every processor. Is this fine?
        endif;

      case AckO:
        if p.hasBackupToken & !p.hasOwnerToken then    -- Must be in Backup state
          BroadcastFaultMsg(AckBD, msg.src, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
          p.hasBackupToken := false;
          undefine p.val;
        endif;

      case AckBD:
        if !p.hasBackupToken & p.hasOwnerToken then    -- In blocked ownership state
          p.hasBackupToken := true;
        endif;

      case Tokens:
        if !isundefined(p.curPersistentRequester) & p.curPersistentRequester != p & msg.serialId = p.curSerial
        then
          -- Forward received tokens to persistent requester (that's not self)
          BroadcastFaultMsg(Tokens, p.curPersistentRequester, p, msg.val, msg.numSharerTokens, msg.hasOwnerToken, msg.serialId);
        else
          ReceiveTokens(p, msg);
        endif;
        
    endswitch;

    endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)

ruleset n: Proc Do
    alias p: Procs[n] do

    --==== Store ====--
    ruleset v: Value do

        
    endruleset;

    --==== Load ====--

    --==== Writeback ====--

    endalias; -- p
endruleset;

-- Message delivery rules per node
ruleset n: Node do

  alias faultChan : FaultNet[n] do

  -- Rule to receive token recreation related messages
  alias tr_msg : TrNet[n] do
  rule "receive-TR-msg"
    (HasTRMsg(n))
  ==>
    if IsMember(n, Home)
    then
      HomeReceive(tr_msg);
    else
      ProcReceive(n, tr_msg);
    endif;
  endrule;
  endalias; -- tr_msg


  -- Rule to delete or process message
  choose midx : faultChan do
    alias msg : faultChan[midx] do

    rule "inject-fault"
      -- TODO: do we need a bit to ensure forward progress?
      -- I dont think so since Murphi will collapse circular states
      MultiSetRemove(faultIdx, faultChan);
    endrule;

    rule "process-message"
      (!HasTRMsg(n))  -- TR messages take priority
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(n, msg);
      endif;
    endrule;

    endalias; -- msg

  endchoose; -- midx

  endalias; -- faultChan

endruleset;



----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate
    -- TBD: Update this
    For v: Value do
        -- home node initialization
        MainMem.state := H_I;
        undefine MainMem.owner;
        MainMem.val := v;
    endfor;
    LastWrite := MainMem.val;
    
    -- processor initialization
    for i: Proc do
        Procs[i].state := P_I;
        undefine Procs[i].val;
        Procs[i].acks := 0;
        Procs[i].acksGot := 0;
    endfor;

    -- network initialization
    undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
  MainMem.state = H_I
    ->
      IsUndefined(MainMem.owner);

invariant "value in memory matches value of last write, when invalid or shared"
     MainMem.state = H_I | MainMem.state = H_S
    ->
      MainMem.val = LastWrite;

invariant "values in valid state match last write"
  Forall n : Proc Do  
     Procs[n].state = P_S | Procs[n].state = P_M
    ->
      Procs[n].val = LastWrite -- LastWrite is updated whenever a new value is created 
  end;
  
invariant "value is undefined while invalid"
  Forall n : Proc Do  
     Procs[n].state = P_I
    ->
      IsUndefined(Procs[n].val)
  end;
  
-- Here are some invariants that are helpful for validating shared state.

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do  
     MainMem.state = H_S | MainMem.state = H_I
    ->
      MainMem.val = LastWrite
  end;

invariant "values in shared state match memory"
  Forall n : Proc Do  
     MainMem.state = H_S & Procs[n].state = P_S
    ->
      MainMem.val = Procs[n].val
  end;

-- Token invariants from paper

invariant "Write Rule"
  Forall n : Proc Do  
    Procs[n].state = P_M
    ->
    Procs[n].hasOwnerToken = true & Procs[n].hasBackupToken = true
  end;

invariant "Read Rule"
  Forall n : Proc Do  
    Procs[n].state = P_S
    ->
    Procs[n].hasOwnerToken = false & Procs[n].hasBackupToken = false
  end;

invariant "Valid-Data Bit Rule"
  Forall n : Proc Do  
    Procs[n].numTokens = 0 | (Procs[n].numTokens = 1 & Procs[n].hasBackupToken)
    ->
    isundefined(Procs[n].val)
  end;

invariant "Maximum of one owned token"
  Forall n : Proc Do  
    Procs[n].hasOwnerToken = true
    ->
        Forall i : Proc Do 
            if (Procs[n] != Procs[i])
            then
                Procs[i].hasOwnerToken = false
            endif;
        end; 
  end;

invariant "Maximum of one backup token"
  Forall n : Proc Do  
    Procs[n].hasBackupToken = true
    ->
        Forall i : Proc Do 
            if (Procs[n] != Procs[i])
            then
                Procs[i].hasBackupToken = false
            endif;
        end;
  end;

invariant "Backup state implies no tokens except backup"
  Forall n : Proc Do
    Procs[n].state = B
    ->
      Procs[n].hasBackupToken = true & Procs[n].numSharerTokens = 0
       & Procs[n].hasOwnerToken = false
  end;