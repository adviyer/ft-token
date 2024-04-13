
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
    };

    
    Message:
        Record
            mtype: MessageType;
            src: Node;
            val: Value;
            numSharerTokens: SharerTokenCount;
            hasOwnerToken: boolean;
            hasBackupToken: boolean;
            serialNum: SerialNumType;
        End;

    HomeState:
        Record
            state: enum {
                -- TBD: Fill this
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
                , Ir
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
Procedure Send(
    mtype: MessageType;
    dst: Node;
    src: Node;
    vc: VCType;
    val: Value;
    numToken: TokenCount;
    hasOwnerToken: boolean;
    hasBackupToken: boolean;
    serialId: SerialType;
);
var msg: Message;
Begin
    
    assert(hasOwnerToken -> !isundefined(val)) "Data Transfer Rule violated";
    assert(hasOwnerToken -> !hasBackupToken)) "Owner Token Transfer Rule violated";
    assert(hasOwnerToken -> Procs[src].hasBackupToken)) "Blocked Ownership Rule violated";
    msg.mtype           := mtype;
    msg.src             := src;
    msg.vc              := vc;
    msg.val             := val;
    msg.numAcks         := numAcks;
    msg.numToken        := numToken;
    msg.hasOwnerToken   := hasOwnerToken;
    msg.hasBackupToken  := hasBackupToken;
    msg.serialId        := serialId;
    if (msg.mtype = IncSerialNum | 
        msg.mtype = BackupInv | 
        msg.mtype = DestructionDone | 
        msg.mtype = StartTokenRec)
    then
        TrNet[dst] := msg;
    else
        assert(MultiSetCount(i: FaultNet[dst], true) < NetMax) "Too many messages";
        MultiSetAdd(msg, FaultNet[dst]);
    endif;
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
    error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
    error "Unhandled state!";
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
    msg_processed := true;

    switch MainMem.state

    endswitch;
End;


Procedure ProcReceive(msg: Message; p: Proc);
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at proc "; put p; put "\n";
-- RECEIVING ORDER: TrNET > Persistent msg in FaultNet > Other msg in faultnet

    -- default to 'processing' message.  set to false otherwise
    msg_processed := true;

    alias ps: Procs[p].state do
    alias pv: Procs[p].val do

    switch ps
          
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
      -- I don't think so since Murphi will collapse circular states
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