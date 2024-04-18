
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
    PerfMsgCount: 0..MaxPerfMsgs; -- number of repeat requests before persistent
    SerialNumType: 0..MaxTokenSerialNum;
    AckCount: 0..(ProcCount-1);

    MessageType: enum {
        -- Regular transient requests
          GetS
        , GetM

        -- Persistent requests (starvation)
        , ActivatePersistent
        , DeactivatePersistent
        , PingPersistent           -- consequence of lost persistent deactivate timeout

        -- Ownership transfer specific messages
        , AckO                     -- owner acknowledgement
        , AckBD                    -- backup deletion acknowledgement
        , Tokens                   -- token transfer message type

        -- Token recreation specific messages
        , StartTokenRec            -- (TRNet) start token recreation (only home can receive)
        , SetSerialNum             -- (TRNet)
        , SetSerialNumAck
        , BackupInv                -- (TRNet)
        , BackupInvAck
        , DestructionDone          -- (TRNet) check data field to indicate DestructionDone with data
    };

    
    Message:
        Record
            mtype: MessageType;
            src: Node;
            dst: Node;
            val: Value;
            numSharerTokens: SharerTokenCount;
            hasOwnerToken: boolean;
            serialId: SerialNumType;
        End;

    HomeState:
        Record
            val: Value;
            numSharerTokens: SharerTokenCount;
            hasOwnerToken: boolean;
            hasBackupToken: boolean;
            curSerial: SerialNumType; -- Main memory needs to know the current token serial number as well
            curPersistentRequester: Proc;
            persistentTable: array [Proc] of boolean;
            isRecreating: boolean;  -- Process of token recreation cannot be superceded (TODO: This might not be necessary if keeping track of TrRequester)
            TrSAckCount: AckCount;
            BInvAckCount: AckCount;
            OwnerAck: boolean;  -- This indicates (in token recreation), whether the home node received the owner token or not.
                                -- (contd.) If true and there is a token recreation timeout, resend BInv with new UNIQUE serial
                                -- number (not token ID). If false and there is a token recreation timeout, increment curSerial
                                -- and broadcast new TrS message
            tokenRecRequester: Node;  -- TODO: Set this whenever a token recreation request is initiated. Token recreation can
                                      -- (contd.) be initiated by the HomeNode (via Lost Data, Backup Timeout) or any processors
                                      -- (contd.) sending a StartTokenRec
        End;

    ProcState:
        Record
            val: Value;
            numSharerTokens: SharerTokenCount;
            hasOwnerToken: boolean;
            hasBackupToken: boolean;
            curSerial: SerialNumType;
            curPersistentRequester: Proc;
            persistentTable: array [Proc] of boolean;

            -- The following fields are used for rulesets:
            desiredState : enum {
              INVALID,
              SHARED,
              MODIFIED
            };
            numPerfMsgs: PerfMsgCount;

        End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
    MainMem:  HomeState;
    Procs: array [Proc] of ProcState;
    FaultNet: array [Node] of multiset [NetMax] of Message;  -- Performance and persistent messages, can be deleted
    TrNet: array [Node] of Message;                          -- Token recreation messages, cosmic ray proof, never deleted
    LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------

-- Checks whether message is a transient request
Function IsTRMsg(msg:Message) : boolean;
Begin
  return (msg.mtype = SetSerialNum |
          msg.mtype = BackupInv | 
          msg.mtype = DestructionDone | 
          msg.mtype = StartTokenRec |
          msg.mtype = SetSerialNumAck);
End;

Procedure BroadcastFaultMsg (
    mtype: MessageType;
    dst: Node;
    src: Node;
    val: Value;
    numSharerTokens: SharerTokenCount;
    hasOwnerToken: boolean;
    serialId: SerialNumType;
);
var msg: Message;
Begin
    assert(!IsTRMsg(msg)); -- checking it isn't a transient request
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
    for n : Node do
      assert(MultiSetCount(i: FaultNet[n], true) < NetMax) "Too many messages";
      MultiSetAdd(msg, FaultNet[n]);
    end;
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

Procedure ReceiveTokens(n:Node; msg:Message);
Begin
    alias p : Procs[n] do

    assert(msg.mtype = Tokens);

    -- Receive tokens
    if p.curSerial = msg.serialId -- checking for message validity
    then
      assert(!isundefined(msg.numSharerTokens));
      p.numSharerTokens := p.numSharerTokens + msg.numSharerTokens;
      if !IsUndefined(msg.val)
      then
      p.val := msg.val;
      endif;

      if msg.hasOwnerToken
      then
        assert(!isundefined(msg.val));
        assert(isundefined(p.hasOwnerToken));
        p.hasOwnerToken := true;
        BroadcastFaultMsg(AckO, msg.src, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
      endif;

      -- resetting perfMsgCount as request is satisfied
      p.numPerfMsgs := 0;
    endif;
    
    endalias; -- p
End;

-- The PersistentTableActivate procedure addresses the issue of processor starvation by 
-- activating a persistent request for a processor (rqstr), ensuring progress when required resources (tokens) are unavailable. 
-- It marks the processor's persistent request as active in the persistentTable.
-- It prioritizes the request by updating the current persistent requester (curPersistentRequester) to the current processor if 

Procedure PersistentTableActivate(rqstr:Proc);
Begin
  alias p : Procs[rqstr] Do

  p.persistentTable[rqstr] := true;

  if isundefined(p.curPersistentRequester) | rqstr < p.curPersistentRequester
  then
    p.curPersistentRequester := rqstr;
  end;

  endalias; -- p
End;

Procedure PersistentTableDeactivate(rqstr:Proc);
Begin
  alias p : Procs[rqstr] Do

  p.persistentTable[rqstr] := false;
  undefine p.curPersistentRequester;

  Forall n : Node Do
    if p.persistentTable[n] = true & IsUndefined(p.curPersistentRequester) 
    then
      p.curPersistentRequester := Procs[n];
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

Function IsInvalid(n:Proc) : boolean;
Begin
  return Procs[n].numSharerTokens = 0 & !Procs[n].hasBackupToken & !Procs[n].hasOwnerToken
End;


Function IsShared(n:Proc) : boolean;
Begin
  return Procs[n].numSharerTokens > 0 | Procs[n].hasOwnerToken;
End;

-- Note: does not consider backup token
Function IsModified(n:Proc) : boolean;
Begin
  return Procs[n].numSharerTokens = MaxSharerTokens & Procs[n].hasOwnerToken;
End;

Procedure NukeAliasSerialTag(serialId: SerialType);
Begin
  for m:FaultNet do
    if FaultNet[m].seriaId = serialId
    then
      MultiSetRemove( m, FaultNet)
    endif;
  endfor;
End

Procedure HomeReceive(msg:Message);
Begin
 alias h : MainMem do
    -- Debug output may be helpful:
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put MainMem.state;

    -- default to 'processing' message.  set to false otherwise
    switch msg.mtype
      case GetS:
        if !h.isRecreating -- Do not send out owner token if in recreation state
        then
          if h.hasOwnerToken & h.hasBackupToken & (h.numSharerTokens = MaxNumSharers) -- State M
          then
            BroadcastFaultMsg(Tokens, msg.src, h, h.val, h.numSharerTokens, true, h.curSerial);
            h.hasOwnerToken := false;
            h.numSharerTokens := 0;
          else if h.hasOwnerToken & (h.numSharerTokens > 0) -- State O/Ob/Mb with more than 1 sharer
          then
              BroadcastFaultMsg(Tokens, msg.src, h, h.val, 1, false, h.curSerial);
              h.numSharerTokens := 0;
          else if h.hasOwnerToken & h.hasBackupToken -- State O; no sharers
          then
            BroadcastFaultMsg(Tokens, msg.src, h, h.val, 0, true, h.curSerial);
            h.hasOwnerToken := false;
          endif;
        endif;

      case GetM:
        if !h.isRecreating  -- Do not send out owner token if in recreation state
        then
          SendAllTokens(msg.src, h);
        endif;

      case StartTokenRec:
        h.numSharerTokens := 0;
        -- NOTE: We could, but shouldn't, delete or send out the owner token if we have it
        if h.curSerial = 3
        then
          h.curSerial := 0;
        else
          h.curSerial := h.curSerial + 1;
        endif;
        -- TODO: add a condition where messages currently in network with "new"" serial number get removed
        -- assumption that serial number will be large enough that serial numbers won't wrap around—should have triggered persistent/regen request
        BroadcastFaultMsg(SetSerialNum, UNDEFINED, HomeType, UNDEFINED, UNDEFINED, UNDEFINED, h.curSerial);
        NukeAliasSerialTag();
      
      case SetSerialNumAck:
        if msg.seriaId = h.curSerial
        then
          assert(h.isRecreating)
            "Main memory received correct SetSerialNumAck without being in recreation state";
          h.TrSAckCount := h.TrSAckCount + 1;
          if !IsUndefined(msg.val)  -- TrS + Data
            assert(h.hasOwnerToken = false)
              "Main memory has owner token when some other processor thinks it has the owner token";
            h.hasOwnerToken := true;
            h.val := msg.val; -- Copy data to memory
          endif;
          if h.TrSAckCount = ProcCount -- Every processor set new serial number
          then
            if h.hasOwnerToken
            then
              if h.hasBackupToken -- Memory has every token it needs to recreate
              then
                if h.tokenRecRequester = HomeType -- Initiator of token recreation was memory
                then
                  h.numSharerTokens := MaxNumSharers;
                  undefine h.tokenRecRequester;
                  h.isRecreating := false;
                else  -- Initiator of token recreation was a processor
                  BroadcastFaultMsg(DestructionDone, h.tokenRecRequester, HomeType, h.val, MaxNumSharers, true, h.curSerial);
                  h.numSharerTokens := 0;
                  h.hasOwnerToken := false;
                  undefine h.tokenRecRequester;
                  h.isRecreating := false;
                endif;
              else -- Memory has owner but not backup
                BroadcastFaultMsg(BackupInv, UNDEFINED, HomeType, UNDEFINED, UNDEFINED, UNDEFINED, h.curSerial);
              endif;
            else  -- Memory does not have owner or backup token
              BroadcastFaultMsg(DestructionDone, h.tokenRecRequester, HomeType, UNDEFINED, 0, false, h.curSerial);
            endif;
          endif;
        endif;

      case BackupInvAck:
        if msg.seriaId = h.curSerial
        then
          h.BInvAckCount := h.BInvAckCount + 1;
          if h.BInvAckCount = ProcCount then
            h.hasBackupToken := true;
            BroadcastFaultMsg(DestructionDone, h.tokenRecRequester, HomeType, h.val, MaxNumSharers, true, h.curSerial);
            h.numSharerTokens := 0;
            h.hasOwnerToken := false;
            undefine h.tokenRecRequester;
            h.isRecreating := false;
          endif;
        endif;

      case DestructionDone:
      -- Ignore

      case ActivatePersistent:
        PersistentTableActivate(msg.src);
        -- Memory can never be the persistent requester
        SendAllTokens(h.curPersistentRequester, HomeType);

      case DeactivatePersistent:
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
        if p.hasOwnerToken & p.hasBackupToken & (p.numSharerTokens = MaxNumSharers) -- State M
        then
          BroadcastFaultMsg(Tokens, msg.src, p, p.val, p.numSharerTokens, true, p.curSerial);
          p.hasOwnerToken := false;
          p.numSharerTokens := 0;
        else if p.hasOwnerToken & (p.numSharerTokens > 0) -- State O/Ob/Mb with more than 1 sharer
        then
            BroadcastFaultMsg(Tokens, msg.src, p, p.val, 1, false, p.curSerial);
            p.numSharerTokens := 0;
        else if p.hasOwnerToken & p.hasBackupToken -- State O; no sharers
        then
          BroadcastFaultMsg(Tokens, msg.src, p, p.val, 0, true, p.curSerial);
          p.hasOwnerToken := false;
        endif;

      case GetM:
        SendAllTokens(msg.src, h);

      case SetSerialNum:
        p.curSerial := msg.serialId;
        if p.hasOwnerToken & !p.hasBackupToken -- State Ob/Mb
        then
          SendTRMsg(SetSerialNumAck, MainMem, p, p.val); -- TODO: Change this "send" message type as we want an unguaranteed broadcast and serial ID
          p.numSharerTokens := 0;
          -- p.hasOwnerToken := false; (cannot delete owner token until you see BInv) (CORRECT)
        else
          SendTRMsg(SetSerialNumAck, MainMem, p, UNDEFINED); -- TODO: Like before, don't use "SendTRMsg" as we need serial ID with this ack
          p.numSharerTokens := 0;
        endif;

      case BackupInv:
        assert(p.numSharerTokens = 0)
          "Processor has sharer tokens when every valid token was deleted from system";
        p.hasOwnerToken := false; -- Now if in state Mb/Ob you can get rid of data as memory is guaranteed to have owner token
        p.hasBackupToken := false;

      case DestructionDone:
        if !IsUndefined(msg.val) -- Destruction done w/ data
        then
          assert(!(p.hasBackupToken | p.numSharerTokens > 0 | p.hasOwnerToken))
            "Processor received TrDone+Data while not being in Invalid";
          p.val := msg.val;
          p.numSharerTokens := MaxNumSharers; -- TODO: Don't we need to send these newly created tokens to the current persistent requester?
          p.hasOwnerToken := true; -- Should go to "state" Mb
        else  -- Destruction done w/o data
          if p.hasBackupToken
          then
            p.numSharerTokens := MaxSharerTokens;
            p.hasOwnerToken := true;
          endif;
        endif;

      case ActivatePersistent:
        PersistentTableActivate(msg.src);
        -- if I am not the persistent requester, send all tokens
        if p != p.curPersistentRequester
        then
          SendAllTokens(p.curPersistentRequester, p);
        endif;

      case DeactivatePersistent:
        PersistentTableDeactivate(msg.src);

      case PingPersistent: -- 
        if !IsEntry(p) then -- not already in persistent table
         BroadcastFaultMsg(DeactivatePersistent, UNDEFINED, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED); -- TODO: I currently have msg.dst as UNDEFINED as this message is meant for every processor. Is this fine?
        endif;

      case AckO: -- ownership has been transfered, data safe to destroy
        if p.hasBackupToken & !p.hasOwnerToken then    -- Must be in Backup state
          BroadcastFaultMsg(AckBD, msg.src, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
          p.hasBackupToken := false;
          undefine p.val;
        endif;

      case AckBD: -- previous backup has been destroyed
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

    alias h : MainMem do

    --==== Store ====--
    ruleset v: Value do

      rule "store while modified"
        (IsModified(p))
      ==>
        p.val := v;
        LastWrite := v;
      endrule;
        
    endruleset;

    rule "store while invalid"
      (p.desiredState = INVALID & IsInvalid(p))
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := MODIFIED;
      assert(!IsEntry(p));
    endrule;

    rule "store while shared"
      (p.desiredState = SHARED & IsShared(p))  
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := MODIFIED; 
      assert(!IsEntry(p));
      
    endrule;

    --==== Load ====--
    rule "load while invalid"
      (p.desiredState = INVALID & IsInvalid(p))
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := SHARED;
      assert(!IsEntry(p));
    endrule;

    --==== Writeback ====--

    rule "evict while shared"
      (p.desiredState = SHARED & IsShared(p) & (!p.hasOwnerToken | p.hasBackupToken))  
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := INVALID; 
      assert(!IsEntry(p));
    endrule;

    rule "evict while owned"
      (p.desiredState = MODIFIED & IsModified(p) & p.hasBackupToken)
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := INVALID;
      assert(!IsEntry(p));
    endrule;

    --==== Performance Messages ====--
    rule "send GetS"
      (!IsShared(p) & desiredState = SHARED & p.numPerfMsgs < MaxPerfMsgs)
    ==>
      BroadcastFaultMsg(GetS, UNDEFINED, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
      p.numPerfMsgs = p.numPerfMsgs + 1;
      assert(!IsEntry(p));
    endrule;

    rule "send GetM"
      (!IsModified(p) & desiredState = MODIFIED & p.numPerfMsgs < MaxPerfMsgs)
    ==>
      BroadcastFaultMsg(GetM, UNDEFINED, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
      p.numPerfMsgs =  p.numPerfMsgs + 1;
      assert(!IsEntry(p));
    endrule;

    --==== Performance Messages ====--
    rule "send persistent request for sharer"
      (!IsShared(p) & desiredState = SHARED & p.numPerfMsgs = MaxPerfMsgs & !IsEntry(p))
    ==>
      PersistentTableActivate(p);
      BroadcastFaultMsg(ActivatePersistent, UNDEFINED, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
      assert(IsEntry(p));
    endrule;

    rule "send persistent request for modifier"
      (!IsModified(p) & desiredState = MODIFIED & p.numPerfMsgs = MaxPerfMsgs & !IsEntry(p))
    ==>
      PersistentTableActivate(p);
      BroadcastFaultMsg(ActivatePersistent, UNDEFINED, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
      assert(IsEntry(p));
    endrule;

    --==== Lost Token Timeouts ===--

    rule "lost backup deletion acknowledgement" -- TODO: do we need to check for whether token is recreating?
      (IsModified(p) & p.hasOwnerToken & !p.hasBackupToken & !h.isRecreating)
    ==> 
      BroadcastFaultMsg(StartTokenRec, p, h, UNDEFINED, UNDEFINED, UNDEFINED);
    endrule

    rule "lost ownership acknowledgement" 
      (!IsModified(p) & p.hasBackupToken & !h.isRecreating)
    ==> 
      BroadcastFaultMsg(StartTokenRec, p, h, UNDEFINED, UNDEFINED, UNDEFINED);

    endalias; -- h
    endalias; -- p
endruleset;

ruleset n: Node do
  

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