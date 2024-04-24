
-- Fault-tolerant token coherence protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 2;          -- number processors
  ValueCount:   2;       -- number of data values.
  NetMax: 10; -- TODO: needs to be a function of MaxPerfMsgs?
  MaxPerfMsgs: 0; -- Number of repeated perf reqs sent before persistent req
  MaxTokenSerialNum: 1;
  MaxSharerTokens: (ProcCount-1);
  MaxFaultsPerTransaction: 3;
  MaxTimeoutAmount: 3;
  
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
    AckCount: 0..(ProcCount);
    FaultCount: 0..MaxFaultsPerTransaction;
    TimeoutCount: 0..MaxTimeoutAmount;

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
            initiator: Node; -- TODO: Confirm that a Proc is always the initiator
            -- faultsInjected: FaultCount;
            -- timeoutAmount: TimeoutCount;
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
	    numDeactivateTimeout: TimeoutCount;
            -- tokenFaultsInjected: array [Proc] of FaultCount;
            -- tokenTimeoutAmount: array [Proc] of TimeoutCount;
            -- persistentFaultTable: array [proc] of FaultCount;
            -- persistentTimeoutTable: array [proc] of TimeoutCount;
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
            -- tokenFaultsInjected: array [Proc] of FaultCount;
            -- tokenTimeoutAmount: array [Proc] of TimeoutCount;
            -- persistentFaultTable: array [proc] of FaultCount;
            -- persistentTimeoutTable: array [proc] of TimeoutCount;
            -- The following fields are used for rulesets:
            numDeactivateTimeout: TimeoutCount;
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
    --TrNet: array [Node] of Message;                          -- TODO: Modify/Delete TrNet as it is no longer cosmic ray proof
    LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware
    tokenFaultsInjected: array [Proc] of FaultCount;
    tokenTimeoutAmount: array [Proc] of TimeoutCount;
    var cnt:0..ProcCount+2;

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------

-- Checks whether message is part of token recreation process
Function IsTRMsg(msg:Message) : boolean;
Begin
  return (msg.mtype = StartTokenRec | 
          msg.mtype = SetSerialNum | 
          msg.mtype = SetSerialNumAck | 
          msg.mtype = BackupInv | 
          msg.mtype = BackupInvAck | 
          msg.mtype = DestructionDone);
End;

Function IsNetFull() : boolean;
Begin
  for n : Node do
    if (MultiSetCount(i: FaultNet[n], true) >= 1)
    then
      return true;
    endif;
  end;
 
return false;
End;

Procedure BroadcastFaultMsg (
    mtype: MessageType;
    dst: Node;
    src: Node;
    val: Value;
    numSharerTokens: SharerTokenCount;
    hasOwnerToken: boolean;
    serialId: SerialNumType;
    initiator: Node;
    -- nextSerialId: SerialNumType; TODO: You might need this if you're having problems with 1 million cycle old TrS messages
);
var msg: Message;
Begin
    -- assert(!IsTRMsg(msg)); -- checking it isn't a transient request
    assert(hasOwnerToken -> !isundefined(val)) "Data Transfer Rule violated";
    -- assert(hasOwnerToken -> Procs[src].hasBackupToken) "Blocked Ownership Rule violated";
    
    msg.mtype           := mtype;
    msg.dst             := dst;
    msg.src             := src;
    msg.val             := val;
    msg.numSharerTokens := numSharerTokens;
    msg.hasOwnerToken   := hasOwnerToken;
    msg.serialId        := serialId;
    msg.initiator	:= initiator;
    -- Iterate through each node's multiset in faultnet and add the message
    
    for n : Node do
      assert(MultiSetCount(i: FaultNet[n], true) < NetMax) "Too many messages";
      if IsUndefined(msg.dst)
      then
        MultiSetAdd(msg, FaultNet[n]);
      elsif msg.dst = n then
        MultiSetAdd(msg, FaultNet[n]);
      endif;
    end;
End;

/*
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
*/

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
        assert(isundefined(p.hasOwnerToken) | p.hasOwnerToken = false);
        if msg.src != HomeType
        then
        assert(Procs[msg.src].hasBackupToken = true) "Owner token sender should have backup token";
        endif;
        p.hasOwnerToken := true;
        BroadcastFaultMsg(AckO, UNDEFINED, n, UNDEFINED, UNDEFINED, false, p.curSerial, UNDEFINED);
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
    recv.numDeactivateTimeout := 0;
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
    BroadcastFaultMsg(Tokens, dst, src, p.val, p.numSharerTokens, true, p.curSerial, dst);  -- TODO: Confirm dst is fine for 'initiator'
    p.numSharerTokens := 0;
    p.hasOwnerToken := false;
  elsif p.hasOwnerToken & p.numSharerTokens > 0 -- State Mb/Ob
  then
    BroadcastFaultMsg(Tokens, dst, src, p.val, p.numSharerTokens, false, p.curSerial, dst);
    p.numSharerTokens := 0;
  elsif p.numSharerTokens > 0 -- State S
  then
    BroadcastFaultMsg(Tokens, dst, src, p.val, p.numSharerTokens, false, p.curSerial, dst);
    p.numSharerTokens := 0;
    undefine p.val;
  endif;

  endalias; -- p
End;

Function IsEntry(p: Proc): boolean;
Begin
  if (isundefined(Procs[p].persistentTable[p]))
  then
    return false;
  else
    return Procs[p].persistentTable[p];
  endif;
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
      MultiSetRemovePred(i: FaultNet[m], !isundefined(FaultNet[m][i].serialId) & FaultNet[m][i].serialId = serialId);
  endfor;
End;

/*
Procedure NukeEverything();
Begin
  for n: Node do
    MultiSetRemovePred(i: FaultNet[n], true);
    Procs[n].hasOwnerToken := false;
    Procs[n].hasBackupToken := false;
    Procs[n].numSharerTokens := 0;
  endfor;
End;
*/

Procedure RecreateTokens();
Begin
  alias h : MainMem do
    h.isRecreating := true;
    h.numSharerTokens := 0;
    h.TrSAckCount := 0;
    h.BInvAckCount := 0;
    -- NOTE: We could, but shouldn't, delete or send out the owner token if we have it
    if h.curSerial = MaxTokenSerialNum
    then
      h.curSerial := 0;
    else
      h.curSerial := h.curSerial + 1;
    endif;
    -- TODO: add a condition where messages currently in network with "new"" serial number get removed
    -- assumption that serial number will be large enough that serial numbers won't wrap around—should have triggered persistent/regen request
    -- NukeEverything();
    NukeAliasSerialTag(h.curSerial);
    BroadcastFaultMsg(SetSerialNum, UNDEFINED, HomeType, UNDEFINED, UNDEFINED, false, h.curSerial, h.tokenRecRequester);
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

Function TokensConserved() : Boolean;
Begin 
  cnt := 0;
  For n : Proc Do  
    cnt := cnt + Procs[n].numSharerTokens;
    if (Procs[n].hasOwnerToken) 
    then 
      cnt := cnt + 1;
    elsif (Procs[n].hasBackupToken)
    then
      cnt := cnt + 1;
    endif;
  End;
  if cnt > ProcCount + 1
  then
    return false;
  else 
    return true;
  endif;
End;

Procedure PrintProcState(n:Proc);
Begin
  alias p : Procs[n] Do
    put "Proc: "; put p.procId;
    put " Owner - "; put p.hasOwnerToken; put " Backup - "; put p.hasBackupToken;
    put " Sharers - "; put p.numSharerTokens; put "\n"; 
  endalias;
End;

Procedure PrintHomeState();
Begin
  alias h : MainMem Do
    put "Home:";
    put " Owner - "; put h.hasOwnerToken; put " Backup - "; put h.hasBackupToken;
    put " Sharers - "; put h.numSharerTokens; put "\n"; 
  endalias;
End;

Procedure PrintAllState();
Begin
  PrintHomeState();
  For n : Proc Do  
    PrintProcState(n);
  endfor;

End;

Procedure HomeReceive(msg:Message);
Begin
 alias h : MainMem do
    -- Debug output may be helpful:

    

    -- default to 'processing' message.  set to false otherwise
    switch msg.mtype
      case GetS:
        if !h.isRecreating -- Do not send out owner token if in recreation state
        then
          if h.hasOwnerToken & h.hasBackupToken & (h.numSharerTokens = MaxSharerTokens) -- State M
          then
            BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, h.numSharerTokens, true, h.curSerial, msg.initiator);
            h.hasOwnerToken := false;
            h.numSharerTokens := 0;
          elsif h.hasOwnerToken & (h.numSharerTokens > 0) -- State O/Ob/Mb with more than 1 sharer
          then
              BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, 1, false, h.curSerial, msg.initiator);
              h.numSharerTokens := h.numSharerTokens - 1;
          elsif h.hasOwnerToken & h.hasBackupToken -- State O; no sharers
          then
            BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, 0, true, h.curSerial, msg.initiator);
            h.hasOwnerToken := false;
          endif;
        endif;

      case GetM:
        if !h.isRecreating  -- Do not send out owner token if in recreation state
        then
          if h.hasOwnerToken & h.hasBackupToken -- State M/O
          then
            BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, h.numSharerTokens, true, h.curSerial, msg.initiator);
            h.numSharerTokens := 0;
            h.hasOwnerToken := false;
          elsif h.hasOwnerToken & h.numSharerTokens > 0 -- State Mb/Ob with 1 or more sharer tokens
          then  -- TODO: Add invariant that if a processor has a sharer token it can load a correct value (i.e. if p.numSharerTokens > 0 => p.val = LastWrite)
            -- NOTE: See commit history. I changed messages that only send sharer tokens when the request wants all tokens to also send data.
            -- (contd.) I did this (wouldn't be necessary in a real system) because we aren't keeping track of previous requests and invariants will fail if sharer
            -- (contd.) tokens do not represent valid data always
            BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, h.numSharerTokens, false, h.curSerial, msg.initiator);
            h.numSharerTokens := 0;
          elsif h.numSharerTokens > 0 -- State S
          then
            BroadcastFaultMsg(Tokens, msg.src, HomeType, h.val, h.numSharerTokens, false, h.curSerial, msg.initiator);
            h.numSharerTokens := 0;
            undefine h.val;
          endif;
        endif;

      case StartTokenRec:
        h.tokenRecRequester := msg.src;
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
                  Assert(!isundefined(h.tokenRecRequester));
		              BroadcastFaultMsg(DestructionDone, h.tokenRecRequester, HomeType, h.val, MaxSharerTokens, true, h.curSerial, msg.initiator);
                  h.numSharerTokens := 0;
                  h.hasOwnerToken := false;
                  undefine h.tokenRecRequester;
                  h.isRecreating := false;
                endif;
              
	     else -- Memory has owner but not backup (Memory was in state Mb/Ob before the TR process)
               BroadcastFaultMsg(BackupInv, UNDEFINED, HomeType, UNDEFINED, UNDEFINED, false, h.curSerial, msg.initiator);
             endif;
            
	    elsif h.OwnerAck  -- Memory did not have the ownership token before the TR process
            then
              BroadcastFaultMsg(BackupInv, UNDEFINED, HomeType, UNDEFINED, UNDEFINED, false, h.curSerial, msg.initiator);  -- TODO: Can memory see this request and does it matter?
            
            else  -- Memory did not receive data from any processor (even after full TR process)
              if h.tokenRecRequester = HomeType -- Memory had the only true backup copy
              then
                assert(h.hasBackupToken)
                  "Memory was the TR requester and wasn't the owner and didn't have backup token (data lost somewhere)";
                h.numSharerTokens := MaxSharerTokens;
                undefine h.tokenRecRequester;
                h.isRecreating := false;
              else -- Some other processor has the true backup copy of the data
                Assert(!isundefined(h.tokenRecRequester));
		            BroadcastFaultMsg(DestructionDone, h.tokenRecRequester, HomeType, UNDEFINED, 0, false, h.curSerial, msg.initiator);
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
            BroadcastFaultMsg(DestructionDone, h.tokenRecRequester, HomeType, h.val, MaxSharerTokens, true, h.curSerial, msg.initiator);
	          Assert(!isundefined(h.tokenRecRequester));
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
	  h.numDeactivateTimeout := 0;
        end;
        -- TODO: Add invariant that memory can never be the persistent requester
        if !h.isRecreating -- If memory is in recreating process, do not send tokens
        then
          if h.hasOwnerToken & h.hasBackupToken -- State M/O
          then
            BroadcastFaultMsg(Tokens, h.curPersistentRequester, HomeType, h.val, h.numSharerTokens, true, h.curSerial, msg.initiator);
            h.numSharerTokens := 0;
            h.hasOwnerToken := false;
          elsif h.hasOwnerToken -- State Mb/Ob
          then
            BroadcastFaultMsg(Tokens, h.curPersistentRequester, HomeType, h.val, h.numSharerTokens, false, h.curSerial, msg.initiator);
            h.numSharerTokens := 0;
          elsif h.numSharerTokens > 0 -- State S
          then
            BroadcastFaultMsg(Tokens, h.curPersistentRequester, HomeType, h.val, h.numSharerTokens, false, h.curSerial, msg.initiator);
            h.numSharerTokens := 0;
            undefine h.val;
          endif;
        endif;

      case DeactivatePersistent:
        h.persistentTable[msg.src] := false;
	h.numDeactivateTimeout := 0;
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
          if h.hasBackupToken & !h.hasOwnerToken
          then
            -- assert(h.hasBackupToken & !h.hasOwnerToken) -- Memory must be in Backup state to get sent this message
              -- "Memory is not in a backup state but it got sent an AckO with the right serial number";
            
	          BroadcastFaultMsg(AckBD, msg.src, HomeType, UNDEFINED, UNDEFINED, false, h.curSerial, msg.initiator);
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
            BroadcastFaultMsg(Tokens, h.curPersistentRequester, HomeType, msg.val, msg.numSharerTokens, msg.hasOwnerToken, msg.serialId, msg.initiator);
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
              BroadcastFaultMsg(AckO, UNDEFINED, HomeType, UNDEFINED, UNDEFINED, false, h.curSerial, msg.initiator);
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
   
    -- put "Receiving "; put msg.mtype; put " at proc "; put p.procId; put "\n";
    

    -- Note: (dst == undefined) -> broadcast
    -- If we are not the intended dst, do nothing
    if (!IsUndefined(msg.dst) & msg.dst != n) | msg.src = n
    then
      return;
    endif;

    switch msg.mtype

      case GetS:    -- README: In TokenB, which FtTokenCMP is based on, procs in S ignore transient read reqs
      -- (contd.) and the proc in O sends the data + 1 token on read request. Migratory sharing optimization is present
        if p.hasOwnerToken & p.hasBackupToken & (p.numSharerTokens = MaxSharerTokens) -- State M
        then
          BroadcastFaultMsg(Tokens, msg.src, n, p.val, p.numSharerTokens, true, p.curSerial, msg.initiator);
          p.hasOwnerToken := false;
          p.numSharerTokens := 0;
        elsif p.hasOwnerToken & (p.numSharerTokens > 0) -- State O/Ob/Mb with more than 1 sharer
        then
            BroadcastFaultMsg(Tokens, msg.src, n, p.val, 1, false, p.curSerial, msg.initiator);
            p.numSharerTokens := p.numSharerTokens - 1;
        elsif p.hasOwnerToken & p.hasBackupToken -- State O; no sharers
        then
          BroadcastFaultMsg(Tokens, msg.src, n, p.val, 0, true, p.curSerial, msg.initiator); -- TODO: confirm whether want to send owner token for getS?
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
            BroadcastFaultMsg(SetSerialNumAck, HomeType, n, p.val, UNDEFINED, true, p.curSerial, msg.initiator);
            p.numSharerTokens := 0;
            p.hasOwnerToken := false; -- Proc will go to state B
          else -- State Mb/Ob
            BroadcastFaultMsg(SetSerialNumAck, HomeType, n, p.val, UNDEFINED, false, p.curSerial, msg.initiator); -- Cannot send Owner token
            p.numSharerTokens := 0; -- Proc will go to state Ob
          endif;
        else -- State S/B/I
          BroadcastFaultMsg(SetSerialNumAck, HomeType, n, UNDEFINED, UNDEFINED, false, p.curSerial, msg.initiator);
          p.numSharerTokens := 0;
          if !p.hasBackupToken
          then
            undefine p.val;
          endif;
        endif;

      case BackupInv:
        if p.curSerial = msg.serialId
        then
          assert(p.numSharerTokens = 0)
            "Processor has sharer tokens when every valid token was deleted from system";
          p.hasOwnerToken := false; -- Now if in state Mb/Ob you can get rid of data as memory is guaranteed to have most recent data
          p.hasBackupToken := false;
	        undefine p.val;
        endif;

      case DestructionDone:
        if msg.serialId = p.curSerial then
          Assert(!isundefined(msg.initiator));
	  tokenFaultsInjected[msg.initiator] := 0;
          tokenTimeoutAmount[msg.initiator] := 0;
          assert(!(p.numSharerTokens > 0 | p.hasOwnerToken))
            "Processor received TrDone while it has non-backup tokens";
          if !IsUndefined(msg.val) -- Destruction done w/ data
          then
            assert(!p.hasBackupToken)
              "Processor received TrDone+Data while not being in Invalid";
            p.val := msg.val;
            p.numSharerTokens := MaxSharerTokens; -- TODO: Don't we need to send these newly created tokens to the current persistent requester?
            p.hasOwnerToken := true; -- Should go to "state" Mb
            if !isundefined(p.curPersistentRequester) & Procs[p.curPersistentRequester].procId != p.procId
            then
              SendAllTokens(p.curPersistentRequester, n); -- TODO: Confirm that this sends every token except the owner token
            else
	            BroadcastFaultMsg(AckO, UNDEFINED, n, UNDEFINED, UNDEFINED, false, p.curSerial, UNDEFINED);
            endif;
          else  -- Destruction done w/o data
            if p.hasBackupToken
            then
              p.numSharerTokens := MaxSharerTokens;
              p.hasOwnerToken := true;
              if !isundefined(p.curPersistentRequester) & Procs[p.curPersistentRequester].procId != p.procId
              then
                SendAllTokens(p.curPersistentRequester, n);
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
        p.numDeactivateTimeout := 0;

      case PingPersistent: -- 
        if !IsEntry(n) then -- not already in persistent table
         BroadcastFaultMsg(DeactivatePersistent, UNDEFINED, n, UNDEFINED, UNDEFINED, false, UNDEFINED, n);
        endif;

      case AckO: -- ownership has been transfered, data safe to destroy
        if msg.serialId = p.curSerial
        then
          if p.hasBackupToken & !p.hasOwnerToken
          then
          -- assert(p.hasBackupToken & !p.hasOwnerToken) -- Processor must be in Backup state to get sent this message
             -- "Processor is not in a backup state but it got sent an AckO with the right serial number";
          BroadcastFaultMsg(AckBD, msg.src, n, UNDEFINED, UNDEFINED, false, p.curSerial, UNDEFINED);
          p.hasBackupToken := false;
          undefine p.val;
	        endif;
        endif;

      case AckBD: -- previous backup has been destroyed
        if msg.serialId = p.curSerial
        then
          assert(!p.hasBackupToken & p.hasOwnerToken) -- Processor must be in state Mb/Ob
            "Processor got sent an AckBD with the right serial number and destination but wasn't in blocked state";
          p.hasBackupToken := true;

          if IsEntry(n) & p.hasBackupToken & p.hasOwnerToken & p.numSharerTokens = MaxSharerTokens
	  then
            BroadcastFaultMsg(DeactivatePersistent, UNDEFINED, n, UNDEFINED, UNDEFINED, false, msg.serialId, UNDEFINED);
	    PersistentTableDeactivate(n, n);
          endif;
        endif;

      case Tokens:
        if msg.serialId = p.curSerial
        then
          if !isundefined(p.curPersistentRequester) & Procs[p.curPersistentRequester].procId != p.procId
          then
            -- Forward received tokens to persistent requester (that's not self)
            if !IsNetFull() then
            BroadcastFaultMsg(Tokens, p.curPersistentRequester, n, msg.val, msg.numSharerTokens, msg.hasOwnerToken, msg.serialId, p.curPersistentRequester);
            endif;
	  else
            ReceiveTokens(n, msg);

 
            if IsEntry(n) & p.hasBackupToken & p.hasOwnerToken & p.numSharerTokens = MaxSharerTokens
            then
	      BroadcastFaultMsg(DeactivatePersistent, UNDEFINED, n, UNDEFINED, UNDEFINED, false, msg.serialId, UNDEFINED);
              PersistentTableDeactivate(n, n);
            endif;
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
      (p.desiredState = INVALID & IsInvalid(n) & !IsNetFull() & !IsEntry(n))
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := MODIFIED;
    endrule;

    rule "store while shared"
      (p.desiredState = SHARED & IsShared(n) & !IsNetFull() & !IsEntry(n))
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := MODIFIED; 
      
    endrule;

    --==== Load ====--
    rule "load while invalid"
      (p.desiredState = INVALID & IsInvalid(n) & !IsNetFull() & !IsEntry(n))
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := SHARED;
    endrule;

    --==== Writeback ====--

    rule "evict while shared"
      (p.desiredState = SHARED & IsShared(n) & (!p.hasOwnerToken | p.hasBackupToken) & !IsNetFull() & !IsEntry(n))  
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := INVALID; 
    endrule;

    rule "evict while owned"
      (p.desiredState = MODIFIED & IsModified(n) & p.hasBackupToken & !IsNetFull() & !IsEntry(n))
    ==>
      p.numPerfMsgs := 0;
      p.desiredState := INVALID;
    endrule;

    --==== Performance Messages ====--
    rule "send GetS"
      (!IsShared(n) & p.desiredState = SHARED & p.numPerfMsgs < MaxPerfMsgs & !IsEntry(n) & !IsNetFull())
    ==>
      BroadcastFaultMsg(GetS, UNDEFINED, n, UNDEFINED, UNDEFINED, false, UNDEFINED, n);
      p.numPerfMsgs := p.numPerfMsgs + 1;
  
    endrule;

    rule "send GetM"
      (!IsModified(n) & p.desiredState = MODIFIED & p.numPerfMsgs < MaxPerfMsgs & !IsEntry(n) & !IsNetFull())
    ==>
      BroadcastFaultMsg(GetM, UNDEFINED, n, UNDEFINED, UNDEFINED, false, UNDEFINED, n);
      p.numPerfMsgs := p.numPerfMsgs + 1;

    endrule;

    --==== Performance Messages ====--
    rule "send persistent request for sharer"
      (!IsShared(n) & p.desiredState = SHARED & p.numPerfMsgs = MaxPerfMsgs & !IsEntry(n) & !IsNetFull())
    ==>
      PersistentTableActivate(n, n);
      BroadcastFaultMsg(ActivatePersistent, UNDEFINED, n, UNDEFINED, UNDEFINED, false, UNDEFINED, n);
      assert(IsEntry(n));
    endrule;

    rule "send persistent request for modifier"
      (!IsModified(n) & p.desiredState = MODIFIED & p.numPerfMsgs = MaxPerfMsgs & !IsEntry(n) & !IsNetFull())
    ==>
      PersistentTableActivate(n, n);
      BroadcastFaultMsg(ActivatePersistent, UNDEFINED, n, UNDEFINED, UNDEFINED, false, UNDEFINED, n);
      assert(IsEntry(n));
    endrule;


    --==== Lost Token Timeouts ===--

    rule "lost token timeout"
      (!isundefined(p.curPersistentRequester) & !h.isRecreating 
      & !IsNetFull() & tokenTimeoutAmount[n] < MaxTimeoutAmount)
    ==>
      BroadcastFaultMsg(StartTokenRec, HomeType, n, UNDEFINED, UNDEFINED, false, UNDEFINED, n); -- TODO: Note messages that initiate TR cannot be destroyed as 
                                                                                                -- destroying it has no effect on coherence and just clutters our states
      tokenTimeoutAmount[n] := tokenTimeoutAmount[n] + 1;
    endrule;


    rule "lost persistent deactivation timeout"
      (!isundefined(p.curPersistentRequester) & Procs[p.curPersistentRequester].procId != p.procId & !IsNetFull()
        & p.numDeactivateTimeout < MaxTimeoutAmount)
    ==>
      BroadcastFaultMsg(PingPersistent, p.curPersistentRequester, n, UNDEFINED, UNDEFINED, false, UNDEFINED, p.curPersistentRequester);
      p.numDeactivateTimeout := p.numDeactivateTimeout + 1;
    endrule;
    
    rule "lost backup deletion acknowledgement" -- TODO: do we need to check for whether token is recreating?
      (IsModified(n) & p.hasOwnerToken & !p.hasBackupToken & !h.isRecreating  & !IsNetFull() & tokenTimeoutAmount[n] < MaxTimeoutAmount)
    ==> 
      BroadcastFaultMsg(StartTokenRec, HomeType, n, UNDEFINED, UNDEFINED, false, UNDEFINED, n);
      tokenTimeoutAmount[n] := tokenTimeoutAmount[n] + 1;
    endrule;

    rule "lost ownership acknowledgement" 
      (!IsModified(n) & p.hasBackupToken & !h.isRecreating  & !IsNetFull() & tokenTimeoutAmount[n] < MaxTimeoutAmount)
    ==> 
      BroadcastFaultMsg(StartTokenRec, HomeType, n, UNDEFINED, UNDEFINED, false, UNDEFINED, n);
      tokenTimeoutAmount[n] := tokenTimeoutAmount[n] + 1;
    endrule;

    endalias; -- h
    endalias; -- p
endruleset;

rule "token recreation timeout"
  (MainMem.isRecreating & !IsNetFull() & tokenTimeoutAmount[MainMem.tokenRecRequester] < MaxTimeoutAmount)
==>
  RecreateTokens();
  tokenTimeoutAmount[MainMem.tokenRecRequester] := tokenTimeoutAmount[MainMem.tokenRecRequester] + 1;
endrule;

rule "home lost persistent deactivation timeout"
  (!isundefined(MainMem.curPersistentRequester) & !IsNetFull()
    & MainMem.numDeactivateTimeout < MaxTimeoutAmount)
    ==>
      MainMem.numDeactivateTimeout := MainMem.numDeactivateTimeout + 1;
      BroadcastFaultMsg(PingPersistent, MainMem.curPersistentRequester, HomeType, UNDEFINED, UNDEFINED, false, UNDEFINED, MainMem.curPersistentRequester);
endrule;

-- Message delivery rules per node
ruleset n: Node do

  -- Rule to delete or process message
  choose midx : FaultNet[n] do
    alias faultChan : FaultNet[n] do
    alias msg : faultChan[midx] do

    rule "inject-fault"
      (!isundefined(msg.mtype))
      ==>
        if ((isundefined(msg.initiator) | (IsTRMsg(msg) & tokenFaultsInjected[msg.initiator] < MaxFaultsPerTransaction 
        & tokenTimeoutAmount[msg.initiator] < MaxTimeoutAmount & msg.mtype != StartTokenRec)) & msg.mtype != DeactivatePersistent & msg.mtype != PingPersistent)
        then
        
	  MultiSetRemove(midx, faultChan);
          
	  if !isundefined(msg.initiator)
	  then
	    tokenFaultsInjected[msg.initiator] := tokenFaultsInjected[msg.initiator] + 1;
          endif;

	elsif !IsMember(n, Home) & Procs[n].numDeactivateTimeout < MaxTimeoutAmount then 
          MultiSetRemove(midx, faultChan);
	
	elsif IsMember(n, Home) & MainMem.numDeactivateTimeout < MaxTimeoutAmount then 
          MultiSetRemove(midx, faultChan);
	endif;
    endrule;

    rule "process-message"
    (!isundefined(msg.mtype))
      ==>
      if IsMember(n, Home)
      then
        if !(MainMem.isRecreating & msg.mtype = StartTokenRec)
        then
            HomeReceive(msg);
            MultiSetRemove(midx, faultChan);
        endif;
      else
        ProcReceive(msg, n);
        MultiSetRemove(midx, faultChan);
      endif;

      
    endrule;

    endalias; -- msg
    endalias; -- faultChan


  endchoose; -- midx


endruleset;

----------------------------------------------------------------------
-- Startstate

startstate
    -- TBD: Update this
    For v: Value do
        -- home node initialization
        MainMem.numSharerTokens := MaxSharerTokens;
        MainMem.hasOwnerToken := true;
        MainMem.hasBackupToken := true;
        MainMem.curSerial := 0;
        MainMem.val := v;
        MainMem.isRecreating := false;
        MainMem.TrSAckCount := 0;
        MainMem.OwnerAck := false;
        MainMem.BInvAckCount := 0;
    endfor;
    LastWrite := MainMem.val;
    MainMem.numDeactivateTimeout := 0;
    
    -- processor initialization
    procId := 0;
    for i: Proc do
        tokenTimeoutAmount[i] := 0;
        tokenFaultsInjected[i] := 0;
	MainMem.persistentTable[i] := false;
        Procs[i].procId := procId;
        Procs[i].hasOwnerToken := false;
        Procs[i].hasBackupToken := false;
        Procs[i].numSharerTokens := 0;
        Procs[i].desiredState := INVALID;
        Procs[i].curSerial := 0;
        Procs[i].numPerfMsgs := 0;
        Procs[i].numDeactivateTimeout := 0;
        procId := procId + 1;
        undefine Procs[i].val;
        
        for j: Proc do
	  Procs[i].persistentTable[j] := false;
        endfor;

    endfor; 
    -- network initialization
    
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------
-- Here are some invariants that are helpful for validating shared state.

invariant "values in memory matches value of last write, when shared"
  Forall n : Proc Do
    Procs[n].numSharerTokens > 0
    ->
    Procs[n].val = LastWrite
  end;

-- Token invariants from paper

invariant "Valid-Data Bit Rule"
  Forall n : Proc Do  
    (Procs[n].numSharerTokens = 0 & !Procs[n].hasOwnerToken & !Procs[n].hasBackupToken)
    ->
    isundefined(Procs[n].val)
  end;

invariant "Maximum of one owned token"
    HasMultipleOwners() = false;

invariant "Maximum of one backup token"
    HasMultipleBackups() = false;

invariant "Conservation of Tokens"
    TokensConserved() = true;

/* Is wrong
invariant "Backup state implies no tokens except backup"
  Forall n : Proc Do
    Procs[n].hasBackupToken
    ->
      Procs[n].hasBackupToken = true & Procs[n].numSharerTokens = 0
       & Procs[n].hasOwnerToken = false
  end;
  */
