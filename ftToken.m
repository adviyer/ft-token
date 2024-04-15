
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
            -- Current state must be coherent with token counts
            state: enum {
                  I
                , R     -- Recreating tokens state (entered when a fault is detected and a token recreation process is requested)
                , B
                , S
                , Ob
                , O
                , Mb
                , M
            };
            val: Value;
            numSharerTokens: SharerTokenCount;
            hasOwnerToken: boolean;
            hasBackupToken: boolean;
            req: MessageType;   -- Each proc needs to keep track of what request it is currently waiting a response for so re-issued requests can happen
            curSerial: SerialNumType;
            curPersistentRequester: Node;
            isPersistent: boolean;
            issuedPersistent: boolean;
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


Procedure IncTokenSerialNum(n:Node);
Begin
    if Procs[n].curSerial = MaxTokenSerialNum
    then
      Procs[n].curSerial = 0;
    else
      Procs[n].curSerial = Procs[n].curSerial + 1;
    endif;
End;

Procedure ReceiveTokens(n:Node, msg:Message);
Begin
    alias p : Procs[n] do

    assert(msg.mtype = Tokens);

    -- Receive tokens
    if p.curSerial = msg.serialNum
    then
      p.numSharerTokens := p.numSharerTokens + msg.numSharerTokens;
      
      if msg.hasOwnerToken
      then
        assert(!isundefined(msg.val));
        p.hasOwnerToken := true;
        p.val := msg.val;
      endif;

      if msg.hasBackupToken
      then
        p.hasBackupToken := true;
      endif;
    endif;

    -- Set appropriate state based tokens
    if p.hasOwnerToken
    then

      if p.hasBackupToken
      then  
        if p.numSharerTokens = MaxSharerTokens
        then
          p.state := M;
        else
          p.state := O;
        endif;
      else
        if p.numSharerTokens = MaxSharerTokens
        then
          p.state := Mb;
        else
          p.state := Ob;
        endif;      
      endif;
    
    else

      if p.hasBackupToken
      then  
        p.state := B;
      else
        if p.numSharerTokens > 0
        then
          p.state := S;
        else
          p.state := I;
        endif;      
      endif;
      
    endif;
    
    endalias; -- p
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

    -- Debug output may be helpful:
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put MainMem.state;

    -- default to 'processing' message.  set to false otherwise
    switch MainMem.state

    endswitch;
End;


Procedure ProcReceive(msg: Message; p: Proc);
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at proc "; put p; put "\n";
-- RECEIVING ORDER: TrNET > Persistent msg in FaultNet > Other msg in faultnet

    -- default to 'processing' message.  set to false otherwise

    alias ps: Procs[p].state do
    alias pv: Procs[p].val do
    alias pst: Procs[p].numSharerTokens do
    alias pot: Procs[p].hasOwnerToken do
    alias pbt: Procs[p].hasBackupToken do
    alias pcs: Procs[p].curSerial do
    alias pip: Procs[n].isPersistent do
    alias piss: Procs[n].issuedPersistent do

    switch msg.mtype
      
      case GetS:

      case GetM:

      case IncSerialNum:

      case BackupInv:

      case DestructionDone:

      case ActivatePersistent:

      case DeactivatePersistent:

      case PingPersistent:
        if pip then
          BroadcastFaultMsg(issued)

      case AckO:
        if pbt & !pot then    -- Must be in Backup state
          Send(AckBD, msg.src, p, UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
          pbt := false;
        endif;

      case AckBD:
        if !pbt & pot then    -- In blocked ownership state
          pbt := true;
        endif;

      case Tokens:
        


      
    endswitch;

    switch ps
      case I:
        switch msg.mtype

          case IncSerialNum:
            IncTokenSerialNum(p);
            -- Send inc serial num ack
          
          case DestructionDone:
            
            if !isundefined(msg.val)
            then
              pst := MaxSharerTokens;
              hasOwnerToken := true;
              hasBackupToken := true;
              ps := M;
            else
              -- TODO: restart timeouts
            endif;
          
          case ActivatePersistent:

          case DeactivatePersistent:

          case PingPersistent:

          case Tokens:
            ReceiveTokens(p, msg);
          
        endswitch;

      case B:
        switch msg.mtype:

          case IncSerialNum:
            IncTokenSerialNum();
            -- Send inc ack

          
          case BackupInv:

          case DestructionDone:

          case ActivatePersistent:

          case DeactivatePersistent:

          case PingPersistent:

          case AckO:

          case AckBD:

          case StartTokenRec:

          case Tokens:
        endswitch;
      case S:
        switch msg.mtype:
          case GetS:
            -- TODO: Do we handle this? Currently we don't handle this
          case GetM:
            Send(Tokens, msg.src, p, pv, pst, false, msg.serialId)
          case IncSerialNum:
          
          case BackupInv:

          case DestructionDone:

          case ActivatePersistent:

          case DeactivatePersistent:

          case PingPersistent:

          case AckO:

          case AckBD:

          case StartTokenRec:

          case Tokens:
        endswitch;
      case Ob:
        switch msg.mtype:
          case GetS:
          
          case GetM:

          case IncSerialNum:
          
          case BackupInv:

          case DestructionDone:

          case ActivatePersistent:

          case DeactivatePersistent:

          case PingPersistent:

          case AckO:

          case AckBD:
            pbt := true;
            ps := O;
          case StartTokenRec:

          case Tokens:
        endswitch;
      case O:
        switch msg.mtype:
          case GetS:
            if pst > 0 then
              Send(Tokens, msg.src, p, pv, 1, false, msg.serialId);
              pst := pst - 1;
            else
              Send(Tokens, msg.src, p, pv, 0, true, msg.serialId);
              pot := false;
              ps := B;
            endif;
          case GetM:
            Send(Tokens, msg.src, p, pv, pst, true, msg.serialId);
            pst := 0;
            pot := false;
            ps := B;

          case IncSerialNum:
          
          case BackupInv:

          case DestructionDone:

          case ActivatePersistent:

          case DeactivatePersistent:

          case PingPersistent:

          case AckO:

          case AckBD:

          case StartTokenRec:

          case Tokens:
            ReceiveTokens(p, msg);
        endswitch;
      case Mb:
        switch msg.mtype:
          case GetS:
          
          case GetM:

          case IncSerialNum:
          
          case BackupInv:

          case DestructionDone:

          case ActivatePersistent:

          case DeactivatePersistent:

          case PingPersistent:

          case AckO:

          case AckBD:
            pbt := true;
            ps := M;
          case StartTokenRec:

          case Tokens:
        endswitch;
      case M:
        switch msg.mtype:
          case GetS:
            Send(Tokens, msg.src, p, pv, pst, true, msg.serialId);
            pst := 0;
            pot := false;
            ps := B;
          case GetM:
            Send(Tokens, msg.src, p, pv, pst, true, msg.serialId);
            pst := 0;
            pot := false;
            ps := B;
          case IncSerialNum:
            
          case BackupInv:
            
          case DestructionDone:

          case ActivatePersistent:

          case DeactivatePersistent:

          case PingPersistent:

          case AckO:

          case AckBD:

          case StartTokenRec:

          case Tokens:
        endswitch;          
    endswitch;
    
    endalias;
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