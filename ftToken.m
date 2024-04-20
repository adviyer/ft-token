
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
    ProcIdType: 0..(ProcCount);
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
        , StartTokenRec            -- start token recreation (only home can receive)
        , SetSerialNum
        , SetSerialNumAck
        , BackupInv
        , BackupInvAck
        , DestructionDone          -- check data field to indicate DestructionDone with data
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
            -- nextSerialId: SerialNumType;
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
            isRecreating: boolean;  -- Process of token recreation cannot be superceded
            TrSAckCount: AckCount;
            BInvAckCount: AckCount;
            OwnerAck: boolean;
            tokenRecRequester: Node;
        End;

    ProcState:
        Record
            val: Value;
            procId: ProcIdType;
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
    procId: ProcIdType;
    MainMem:  HomeState;
    Procs: array [Proc] of ProcState;
    FaultNet: array [Node] of multiset [NetMax] of Message;  -- Performance and persistent messages, can be deleted
    TrNet: array [Node] of Message;                          -- TODO: Modify/Delete TrNet as it is no longer cosmic ray proof
    LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------

-- Checks whether message is a transient request
Function IsTRMsg(msg:Message) : boolean;         -- TODO: Delete this once TRNet is fixed
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
    -- nextSerialId: SerialNumType; TODO: You might need this if you're having problems with 1 million cycle old TrS messages
);
var msg: Message;
Begin
    -- assert(!IsTRMsg(msg)); -- checking it isn't a transient request
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

    -- Delete existing message with same serial ID
    for n : Node do
        alias trMsg : TrNet[n] do
            if trMsg.serialId = msg.serialId then
                undefine trMsg;
            endif;
        endalias;
    endfor;

    msg.mtype   := mtype;
    msg.dst     := dst;
    msg.src     := src;
    msg.val     := val;

    TrNet[dst] := msg;
End;

Procedure ErrorUnhandledMsg(msg: Message; n: Node);
Begin
    error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
    error "Unhandled state!";
End;

Procedure ReceiveTokens(n: Node; msg: Message);
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
        BroadcastFaultMsg(AckO, msg.src, n, UNDEFINED, UNDEFINED, false, p.curSerial);
      endif;

      -- resetting perfMsgCount as request is satisfied
      p.numPerfMsgs := 0;   -- TODO: wtf is this for?
    endif;
    
    endalias; -- p
End;

-- The PersistentTableActivate procedure addresses the issue of processor starvation by 
-- activating a persistent request for a processor (rqstr), ensuring progress when required resources (tokens) are unavailable. 
-- It marks the processor's persistent request as active in the persistentTable.
-- It prioritizes the request by updating the current persistent requester (curPersistentRequester) to the current processor if 

Procedure PersistentTableActivate(cur: Proc; rqstr: Proc);
Begin
  alias recv : Procs[cur] Do
  alias req : Procs[rqstr] Do

  recv.persistentTable[rqstr] := true;

  if isundefined(recv.curPersistentRequester)
      | (req.procId < Procs[recv.curPersistentRequester].procId) then
    recv.curPersistentRequester := rqstr;
  end;

  -- Resetting number of performance messages
  req.numPerfMsgs := 0;

  endalias; -- req
  endalias; -- recv
End;

Procedure PersistentTableDeactivate(cur: Proc; rqstr: Proc);
Begin
  alias recv : Procs[cur] Do

  recv.persistentTable[rqstr] := false;
  if rqstr = recv.curPersistentRequester
  then
    undefine recv.curPersistentRequester;
  endif;

  For n : Proc Do
    if recv.persistentTable[n] = true & IsUndefined(recv.curPersistentRequester) 
    then
      recv.curPersistentRequester := n;
    endif;
  End;
  
  endalias; -- recv
End;

Procedure SendAllTokens(dst: Node; src: Proc);
Begin
  alias p: Procs[src] do

  if p.hasOwnerToken & p.hasBackupToken -- State M/O
  then
    BroadcastFaultMsg(Tokens, dst, src, p.val, p.numSharerTokens, true, p.curSerial);
    p.numSharerTokens := 0;
    p.hasOwnerToken := false;
  elsif p.hasOwnerToken -- State Mb/Ob
  then
    BroadcastFaultMsg(Tokens, dst, src, UNDEFINED, p.numSharerTokens, false, p.curSerial);
    p.numSharerTokens := 0;
  elsif p.numSharerTokens > 0 -- State S
  then
    BroadcastFaultMsg(Tokens, dst, src, UNDEFINED, p.numSharerTokens, false, p.curSerial);
    p.numSharerTokens := 0;
    undefine p.val;
  endif;

  endalias; -- p
End;

Function IsEntry(p: Proc): boolean;
Begin
  return Procs[p].persistentTable[p];
End;

/*
Function HasTRMsg(n: Node) : boolean;
Begin
  return !isundefined(TrNet[n]);
End;
*/

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

Procedure NukeAliasSerialTag(serialId: SerialNumType);
Begin
  for m: Node do
      MultiSetRemovePred(i: FaultNet[m], FaultNet[m][i].serialId = serialId);
  endfor;
End;

Procedure RecreateTokens();
Begin
  alias h : MainMem do
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
    NukeAliasSerialTag(h.curSerial);
    BroadcastFaultMsg(SetSerialNum, UNDEFINED, HomeType, UNDEFINED, UNDEFINED, false, h.curSerial);
  endalias;
End;

Function HasMultipleOwners() : Boolean;
Begin 
  For n : Proc Do  
    if Procs[n].hasOwnerToken
    then
      For i : Proc Do 
        if  (Procs[n].procId != Procs[i].procId & Procs[i].hasOwnerToken = true)
        then
          return true;
        end
      end; 
    endif;
  endfor;
  return false;
End;

Function HasMultipleBackups() : Boolean;
Begin 
  For n : Proc Do  
    if Procs[n].hasBackupToken
    then
      For i : Proc Do 
        if  (Procs[n].procId != Procs[i].procId & Procs[i].hasBackupToken = true)
        then
          return true;
        end
      end; 
    endif;
  endfor;
  return false;
End;

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
          if h.hasOwnerToken & h.hasBackupToken & (h.numSharerTokens = MaxSharerTokens) -- State M
          then
            BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, h.numSharerTokens, true, h.curSerial);
            h.hasOwnerToken := false;
            h.numSharerTokens := 0;
          elsif h.hasOwnerToken & (h.numSharerTokens > 0) -- State O/Ob/Mb with more than 1 sharer
          then
              BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, 1, false, h.curSerial);
              h.numSharerTokens := h.numSharerTokens - 1;
          elsif h.hasOwnerToken & h.hasBackupToken -- State O; no sharers
          then
            BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, 0, true, h.curSerial);
            h.hasOwnerToken := false;
          endif;
        endif;

      case GetM:
        if !h.isRecreating  -- Do not send out owner token if in recreation state
        then
          if h.hasOwnerToken & h.hasBackupToken -- State M/O
          then
            BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, h.numSharerTokens, true, h.curSerial);
            h.numSharerTokens := 0;
            h.hasOwnerToken := false;
          elsif h.hasOwnerToken & h.numSharerTokens > 0 -- State Mb/Ob with 1 or more sharer tokens
          then  -- TODO: Add invariant that if a processor has a sharer token it can load a correct value (i.e. if p.numSharerTokens > 0 => p.val = LastWrite)
            -- NOTE: See commit history. I changed messages that only send sharer tokens when the request wants all tokens to also send data.
            -- (contd.) I did this (wouldn't be necessary in a real system) because we aren't keeping track of previous requests and invariants will fail if sharer
            -- (contd.) tokens do not represent valid data always
            BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, h.numSharerTokens, false, h.curSerial);
            h.numSharerTokens := 0;
          elsif h.numSharerTokens > 0 -- State S
          then
            BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, h.numSharerTokens, false, h.curSerial);
            h.numSharerTokens := 0;
            undefine h.val;
          endif;
        endif;

      case StartTokenRec:
        RecreateTokens();
      
      case SetSerialNumAck:
        if msg.serialId = h.curSerial
        then
          assert(h.isRecreating)
            "Main memory received correct SetSerialNumAck without being in recreation state";
          h.TrSAckCount := h.TrSAckCount + 1;
          if !IsUndefined(msg.val)  -- TrS + Data
          then
            assert(h.hasOwnerToken = false)
              "Main memory has owner token when some other processor thinks it has the owner token";
            h.OwnerAck := true; -- This serves as a backup reminder, in case the TR process gets restarted, to send BInv even if you don't
                                -- (contd.) receive TrSAck + Data the 2nd time around
            h.val := msg.val; -- Copy data to memory
          endif;
          if h.TrSAckCount = ProcCount -- Every processor set new serial number
          then
            if h.hasOwnerToken  -- TODO: Add invariant that h.hasOwnerToken & h.OwnerAck are never both true
            then
              if h.hasBackupToken -- Memory has every token it needs to recreate
              then
                if h.tokenRecRequester = HomeType -- Initiator of token recreation was memory
                then
                  h.numSharerTokens := MaxSharerTokens;
                  undefine h.tokenRecRequester;
                  h.isRecreating := false;
                else  -- Initiator of token recreation was a processor
                  BroadcastFaultMsg(DestructionDone, h.tokenRecRequester, HomeType, h.val, MaxSharerTokens, true, h.curSerial);
                  h.numSharerTokens := 0;
                  h.hasOwnerToken := false;
                  undefine h.tokenRecRequester;
                  h.isRecreating := false;
                endif;
              else -- Memory has owner but not backup (Memory was in state Mb/Ob before the TR process)
                BroadcastFaultMsg(BackupInv, UNDEFINED, HomeType, UNDEFINED, UNDEFINED, false, h.curSerial);
              endif;
            elsif h.OwnerAck  -- Memory did not have the ownership token before the TR process
            then
              BroadcastFaultMsg(BackupInv, UNDEFINED, HomeType, UNDEFINED, UNDEFINED, false, h.curSerial);  -- TODO: Can memory see this request and does it matter?
            else  -- Memory did not receive data from any processor (even after full TR process)
              if h.tokenRecRequester = HomeType -- Memory had the only true backup copy
              then
                assert(h.hasBackupToken)
                  "Memory was the TR requester and wasn't the owner and didn't have backup token (data lost somewhere)";
                h.numSharerTokens := MaxSharerTokens;
                undefine h.tokenRecRequester;
                h.isRecreating := false;
              else -- Some other processor has the true backup copy of the data
                BroadcastFaultMsg(DestructionDone, h.tokenRecRequester, HomeType, UNDEFINED, 0, false, h.curSerial);
              endif;
            endif;
          endif;
        endif;

      case BackupInv:
        -- TODO: I don't even think its possible for memory to see this request

      case BackupInvAck:
        if msg.serialId = h.curSerial
        then
          h.BInvAckCount := h.BInvAckCount + 1;
          if h.BInvAckCount = ProcCount then
            h.hasBackupToken := true;
            BroadcastFaultMsg(DestructionDone, h.tokenRecRequester, HomeType, h.val, MaxSharerTokens, true, h.curSerial);
            h.numSharerTokens := 0;
            h.hasOwnerToken := false;
            h.OwnerAck := false;  -- TODO: Add invariant that h.OwnerAck, if h.isRecreating is false, must be false
            undefine h.tokenRecRequester;
            h.isRecreating := false;
          endif;
        endif;

      case DestructionDone:
      -- Ignore

      case ActivatePersistent:

        h.persistentTable[msg.src] := true;

        if isundefined(h.curPersistentRequester)
            | (Procs[msg.src].procId < Procs[h.curPersistentRequester].procId) then
          h.curPersistentRequester := msg.src;
        end;
        -- TODO: Add invariant that memory can never be the persistent requester
        if !h.isRecreating -- If memory is in recreating process, do not send tokens
        then
          if h.hasOwnerToken & h.hasBackupToken -- State M/O
          then
            BroadcastFaultMsg(Tokens, h.curPersistentRequester, HomeType, h.val, h.numSharerTokens, true, h.curSerial);
            h.numSharerTokens := 0;
            h.hasOwnerToken := false;
          elsif h.hasOwnerToken -- State Mb/Ob
          then
            BroadcastFaultMsg(Tokens, h.curPersistentRequester, HomeType, h.val, h.numSharerTokens, false, h.curSerial);
            h.numSharerTokens := 0;
          elsif h.numSharerTokens > 0 -- State S
          then
            BroadcastFaultMsg(Tokens, h.curPersistentRequester, HomeType, h.val, h.numSharerTokens, false, h.curSerial);
            h.numSharerTokens := 0;
            undefine h.val;
          endif;
        endif;

      case DeactivatePersistent:
        h.persistentTable[msg.src] := false;
        if msg.src = h.curPersistentRequester
        then
          undefine h.curPersistentRequester;
        endif;

        For n : Proc Do
          if h.persistentTable[n] = true & IsUndefined(h.curPersistentRequester) 
          then
            h.curPersistentRequester := n;
          endif;
        End;

      case PingPersistent:
        -- Shouldn't ever get pinged

      case AckO:
        if msg.serialId = h.curSerial
        then
          if msg.dst = HomeType
          then
            assert(h.hasBackupToken & !h.hasOwnerToken) -- Memory must be in Backup state to get sent this message
              "Memory is not in a backup state but it got sent an AckO with the right serial number";
            BroadcastFaultMsg(AckBD, msg.src, HomeType, UNDEFINED, UNDEFINED, false, h.curSerial);
            h.hasBackupToken := false;
            undefine h.val;
          endif;
        endif;

      case AckBD:
        if msg.serialId = h.curSerial
        then
          if msg.dst = HomeType
          then
            assert(!h.hasBackupToken & h.hasOwnerToken) -- Memory must be in state Mb/Ob
              "Memory got sent an AckBD with the right serial number and Home destination but wasn't in blocked state";
            h.hasBackupToken := true;
          endif;
        endif;

      case Tokens:
        if (h.curSerial = msg.serialId) & (msg.dst = HomeType) -- checking for message validity and if message is meant for Node
        then
          assert(!IsUndefined(msg.numSharerTokens))
            "Got sent tokens but number of sharer tokens was undefined";
          if !IsUndefined(h.curPersistentRequester)
          then
            -- Forward received tokens to persistent requester (that's not self)
            BroadcastFaultMsg(Tokens, h.curPersistentRequester, HomeType, msg.val, msg.numSharerTokens, msg.hasOwnerToken, msg.serialId);
          else
            h.numSharerTokens := h.numSharerTokens + msg.numSharerTokens;
            if !IsUndefined(msg.val)
            then
              h.val := msg.val;
            endif;

            if msg.hasOwnerToken
            then
              assert(!IsUndefined(msg.val))
                "Got sent owner token but message value was undefined";
              assert(IsUndefined(h.hasOwnerToken))
                "Got sent owner token while currently having the owner token";
              h.hasOwnerToken := true;
              BroadcastFaultMsg(AckO, msg.src, HomeType, UNDEFINED, UNDEFINED, false, h.curSerial);
            endif;
            -- resetting perfMsgCount as request is satisfied
            -- h.numPerfMsgs := 0;  TODO: I don't know wtf this is doing
          endif;
        endif;

    endswitch;
    endalias; -- h
End;


Procedure ProcReceive(msg: Message; n: Proc);
Begin

    alias p: Procs[n] do

    --put "Receiving "; put msg.mtype; put " at proc "; put p; put "\n";

    -- Note: (dst == undefined) -> broadcast
    -- If we are not the intended dst, do nothing
    if !IsUndefined(msg.dst) & msg.dst != n -- TODO: oops I should've just did this solution for HomeNode
    then
      return;
    endif;

    switch msg.mtype

      case GetS:    -- README: In TokenB, which FtTokenCMP is based on, procs in S ignore transient read reqs
      -- (contd.) and the proc in O sends the data + 1 token on read request. Migratory sharing optimization is present
        if p.hasOwnerToken & p.hasBackupToken & (p.numSharerTokens = MaxSharerTokens) -- State M
        then
          BroadcastFaultMsg(Tokens, msg.src, n, p.val, p.numSharerTokens, true, p.curSerial);
          p.hasOwnerToken := false;
          p.numSharerTokens := 0;
        elsif p.hasOwnerToken & (p.numSharerTokens > 0) -- State O/Ob/Mb with more than 1 sharer
        then
            BroadcastFaultMsg(Tokens, msg.src, n, p.val, 1, false, p.curSerial);
            p.numSharerTokens := p.numSharerTokens - 1;
        elsif p.hasOwnerToken & p.hasBackupToken -- State O; no sharers
        then
          BroadcastFaultMsg(Tokens, msg.src, n, p.val, 0, true, p.curSerial); -- TODO: confirm whether want to send owner token for getS?
          p.hasOwnerToken := false;
        endif;

      case GetM:
        SendAllTokens(msg.src, n);

      case SetSerialNum:
        p.curSerial := msg.serialId;
        if p.hasOwnerToken -- State M/Mb/O/Ob
        then
          if p.hasBackupToken -- State M/O
          then
            BroadcastFaultMsg(SetSerialNumAck, HomeType, n, p.val, UNDEFINED, true, p.curSerial);
            p.numSharerTokens := 0;
            p.hasOwnerToken := false; -- Proc will go to state B
          else -- State Mb/Ob
            BroadcastFaultMsg(SetSerialNumAck, HomeType, n, p.val, UNDEFINED, false, p.curSerial); -- Cannot send Owner token
            p.numSharerTokens := 0; -- Proc will go to state Ob
          endif;
        else -- State S/B/I
          BroadcastFaultMsg(SetSerialNumAck, HomeType, n, UNDEFINED, UNDEFINED, false, p.curSerial);
          p.numSharerTokens := 0;
        endif;

      case BackupInv:
        if p.curSerial = msg.serialId
        then
          assert(p.numSharerTokens = 0)
            "Processor has sharer tokens when every valid token was deleted from system";
          p.hasOwnerToken := false; -- Now if in state Mb/Ob you can get rid of data as memory is guaranteed to have most recent data
          p.hasBackupToken := false;
        endif;

      case DestructionDone:
        if msg.serialId = p.curSerial then
          assert(!(p.numSharerTokens > 0 | p.hasOwnerToken))
            "Processor received TrDone while it has non-backup tokens";
          if !IsUndefined(msg.val) -- Destruction done w/ data
          then
            assert(!p.hasBackupToken)
              "Processor received TrDone+Data while not being in Invalid";
            p.val := msg.val;
            p.numSharerTokens := MaxSharerTokens; -- TODO: Don't we need to send these newly created tokens to the current persistent requester?
            p.hasOwnerToken := true; -- Should go to "state" Mb
            BroadcastFaultMsg(AckO, msg.src, n, UNDEFINED, UNDEFINED, false, p.curSerial);
            if !isundefined(p.curPersistentRequester) & Procs[p.curPersistentRequester].procId != p.procId
            then
              SendAllTokens(p.curPersistentRequester, n); -- TODO: Confirm that this sends every token except the owner token
            endif;
          else  -- Destruction done w/o data
            if p.hasBackupToken
            then
              p.numSharerTokens := MaxSharerTokens;
              p.hasOwnerToken := true;
              if !isundefined(p.curPersistentRequester) & Procs[p.curPersistentRequester].procId != p.procId
                then
                SendAllTokens(p.curPersistentRequester, n); -- TODO: Confirm that this sends every token except the owner token
              endif;
            endif;
          endif;
        endif;

      case ActivatePersistent:
        PersistentTableActivate(n, msg.src);
        -- if I am not the persistent requester, send all tokens
        if Procs[p.curPersistentRequester].procId != p.procId
        then
          SendAllTokens(p.curPersistentRequester, n);
        endif;

      case DeactivatePersistent:
        PersistentTableDeactivate(n, msg.src);

      case PingPersistent: -- 
        if !IsEntry(n) then -- not already in persistent table
         BroadcastFaultMsg(DeactivatePersistent, UNDEFINED, n, UNDEFINED, UNDEFINED, false, UNDEFINED); -- TODO: I currently have msg.dst as UNDEFINED as this message is meant for every processor. Is this fine?
        endif;

      case AckO: -- ownership has been transfered, data safe to destroy
        if msg.serialId = p.curSerial
        then
          assert(p.hasBackupToken & !p.hasOwnerToken) -- Processor must be in Backup state to get sent this message
              "Processor is not in a backup state but it got sent an AckO with the right serial number";
          BroadcastFaultMsg(AckBD, msg.src, n, UNDEFINED, UNDEFINED, false, p.curSerial);
          p.hasBackupToken := false;
          undefine p.val;
        endif;

      case AckBD: -- previous backup has been destroyed
        if msg.serialId = p.curSerial
        then
          assert(!p.hasBackupToken & p.hasOwnerToken) -- Processor must be in state Mb/Ob
            "Processor got sent an AckBD with the right serial number and destination but wasn't in blocked state";
          p.hasBackupToken := true;
        endif;

      case Tokens:
        if msg.serialId = p.curSerial
        then
          if !isundefined(p.curPersistentRequester) & Procs[p.curPersistentRequester].procId != p.procId
          then
            -- Forward received tokens to persistent requester (that's not self)
            BroadcastFaultMsg(Tokens, p.curPersistentRequester, n, msg.val, msg.numSharerTokens, msg.hasOwnerToken, msg.serialId);
          else
            ReceiveTokens(n, msg);
          endif;
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
        (IsModified(n))
      ==>
        p.val := v;
        LastWrite := v;
      endrule;
        
    endruleset;

    rule "store while invalid"
      (p.desiredState = INVALID & IsInvalid(n))
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := MODIFIED;
      assert(!IsEntry(n));
    endrule;

    rule "store while shared"
      (p.desiredState = SHARED & IsShared(n))  
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := MODIFIED; 
      assert(!IsEntry(n));
      
    endrule;

    --==== Load ====--
    rule "load while invalid"
      (p.desiredState = INVALID & IsInvalid(n))
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := SHARED;
      assert(!IsEntry(n));
    endrule;

    --==== Writeback ====--

    rule "evict while shared"
      (p.desiredState = SHARED & IsShared(n) & (!p.hasOwnerToken | p.hasBackupToken))  
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := INVALID; 
      assert(!IsEntry(n));
    endrule;

    rule "evict while owned"
      (p.desiredState = MODIFIED & IsModified(n) & p.hasBackupToken)
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := INVALID;
      assert(!IsEntry(n));
    endrule;

    --==== Performance Messages ====--
    rule "send GetS"
      (!IsShared(n) & p.desiredState = SHARED & p.numPerfMsgs < MaxPerfMsgs)
    ==>
      BroadcastFaultMsg(GetS, UNDEFINED, n, UNDEFINED, UNDEFINED, false, UNDEFINED);
      p.numPerfMsgs := p.numPerfMsgs + 1;
      assert(!IsEntry(n));
    endrule;

    rule "send GetM"
      (!IsModified(n) & p.desiredState = MODIFIED & p.numPerfMsgs < MaxPerfMsgs)
    ==>
      BroadcastFaultMsg(GetM, UNDEFINED, n, UNDEFINED, UNDEFINED, false, UNDEFINED);
      p.numPerfMsgs := p.numPerfMsgs + 1;
      assert(!IsEntry(n));
    endrule;

    --==== Performance Messages ====--
    rule "send persistent request for sharer"
      (!IsShared(n) & p.desiredState = SHARED & p.numPerfMsgs = MaxPerfMsgs & !IsEntry(n))
    ==>
      PersistentTableActivate(n, n);
      BroadcastFaultMsg(ActivatePersistent, UNDEFINED, n, UNDEFINED, UNDEFINED, false, UNDEFINED);
      assert(IsEntry(n));
    endrule;

    rule "send persistent request for modifier"
      (!IsModified(n) & p.desiredState = MODIFIED & p.numPerfMsgs = MaxPerfMsgs & !IsEntry(n))
    ==>
      PersistentTableActivate(n, n);
      BroadcastFaultMsg(ActivatePersistent, UNDEFINED, n, UNDEFINED, UNDEFINED, false, UNDEFINED);
      assert(IsEntry(n));
    endrule;

    --==== Lost Token Timeouts ===--

    rule "lost backup deletion acknowledgement" -- TODO: do we need to check for whether token is recreating?
      (IsModified(n) & p.hasOwnerToken & !p.hasBackupToken & !h.isRecreating)
    ==> 
      BroadcastFaultMsg(StartTokenRec, n, HomeType, UNDEFINED, UNDEFINED, false, UNDEFINED);
    endrule;

    rule "lost ownership acknowledgement" 
      (!IsModified(n) & p.hasBackupToken & !h.isRecreating)
    ==> 
      BroadcastFaultMsg(StartTokenRec, n, HomeType, UNDEFINED, UNDEFINED, false, UNDEFINED);
    endrule;

    --==== Token Recreation Timeout ====--
    
    rule "token recreation timeout" 
      (h.isRecreating)
    ==> 
      RecreateTokens();
    endrule;
      
    endalias; -- h
    endalias; -- p
endruleset;

-- Message delivery rules per node
ruleset n: Node do

  alias faultChan : FaultNet[n] do

  -- Rule to delete or process message
  choose midx : FaultNet[n] do
    alias msg : faultChan[midx] do

    rule "inject-fault"
      -- TODO: do we need a bit to ensure forward progress?
      -- I dont think so since Murphi will collapse circular states
      MultiSetRemove(midx, faultChan);
    endrule;

    rule "process-message"
      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
      endif;

      MultiSetRemove(midx, faultChan);
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
        MainMem.numSharerTokens := MaxSharerTokens;
        MainMem.hasOwnerToken := true;
        MainMem.hasBackupToken := true;
        MainMem.curSerial := 0;
        MainMem.val := v;
    endfor;
    LastWrite := MainMem.val;
    
    -- processor initialization
    procId := 0;
    for i: Proc do

        Procs[i].procId := procId;
        Procs[i].hasOwnerToken := false;
        Procs[i].hasBackupToken := false;
        Procs[i].numSharerTokens := 0;
        Procs[i].desiredState := INVALID;
        Procs[i].curSerial := 0;
        Procs[i].numPerfMsgs := 0;

        procId := procId + 1;
        undefine Procs[i].val;

    endfor;

    -- network initialization
    undefine FaultNet;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------
-- Here are some invariants that are helpful for validating shared state.

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do
    Procs[n].numSharerTokens > 0
    ->
    MainMem.val = LastWrite
  end;

-- Token invariants from paper

invariant "Valid-Data Bit Rule"
  Forall n : Proc Do  
    Procs[n].numSharerTokens = 0
    ->
    isundefined(Procs[n].val)
  end;

invariant "Maximum of one owned token"
    HasMultipleOwners() = false;

invariant "Maximum of one backup token"
    HasMultipleBackups() = false;

invariant "Backup state implies no tokens except backup"
  Forall n : Proc Do
    Procs[n].hasBackupToken
    ->
      Procs[n].hasBackupToken = true & Procs[n].numSharerTokens = 0
       & Procs[n].hasOwnerToken = false
  end;
