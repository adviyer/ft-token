
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
    TrNet: array [Node] of multiset [NetMax] of Message; -- Token recreation messages, cosmic ray proof, never deleted
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
    assert(MultiSetCount(i: Net[dst], true) < NetMax) "Too many messages";
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
        MultiSetAdd(msg, TrNet[dst]);
    else
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

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst: Node);
Begin
    for n: Node do
        -- TBD
    endfor;
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
    alias p: Procs[n] Do

    --==== Store ====--

    ruleset v: Value Do

        rule "store-to-modified"
            (p.state = P_M)
        ==>
            p.val := v;
            LastWrite := p.val;
        endrule;

        rule "store-to-exclusive"
            (p.state = P_E)
        ==>
            p.val := v;
            LastWrite := p.val;
            p.state := P_M;
        endrule;

        rule "store-to-shared"
            (p.state = P_S)
        ==>
            Send(GetM, HomeType, n, VC0, undefined, 0);
            p.state := P_SMad;
        endrule;

        rule "store-to-invalid"
            (p.state = P_I)
        ==>
            Send(GetM, HomeType, n, VC0, undefined, 0);
            p.state := P_IMad;
        endrule;
        
    endruleset;

    --==== Load ====--

    -- Shared and Modified states will hit so no need to put rule

    rule "load-from-invalid"
        (p.state = P_I)
    ==>
        Send(GetS, HomeType, n, VC0, undefined, 0);
        p.state := P_ISd;
    endrule;

    --==== Writeback ====--

    rule "writeback-modified"
        (p.state = P_M)
    ==>
        Send(PutM, HomeType, n, VC1, p.val, 0);
        p.state := P_MIa;
        -- p.val is still valid
    endrule;

    rule "writeback-exclusive"
        (p.state = P_E)
    ==>
        Send(PutE, HomeType, n, VC1, undefined, 0);
        p.state := P_MIa; -- EIa is same as MIa
        -- p.val is still valid
    endrule;

    rule "writeback-shared"
        (p.state = P_S)
    ==>
        Send(PutS, HomeType, n, VC0, undefined, 0);
        p.state := P_SIa;
        undefine p.val;
    endrule;

    endalias;
endruleset;

-- Message delivery rules
ruleset n: Node do

  alias trChan : TrNet[n];

  rule "receive-"

  choose midx: FaultNet[n] do
    alias faultChan: FaultNet[n] do
    alias msg: chan[midx] do
    alias box: InBox[n] do



    rule "receive-net"
      (isundefined(box[msg.vc].mtype))
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
      endif;

      if ! msg_processed
      then
        -- The node refused the message, stick it in the InBox to block the VC.
        box[msg.vc] := msg;
      endif;
    
      MultiSetRemove(midx, chan);
    
    endrule;
  
    endalias
    endalias;
    endalias;
  endchoose;  

  -- Try to deliver a message from a blocked VC; perhaps the node can handle it now
  ruleset vc: VCType do
      rule "receive-blocked-vc"
          (! isundefined(InBox[n][vc].mtype))
      ==>
          if IsMember(n, Home)
          then
              HomeReceive(InBox[n][vc]);
          else
              ProcReceive(InBox[n][vc], n);
          endif;

          if msg_processed
          then
              -- Message has been handled, forget it
              undefine InBox[n][vc];
          endif;
      
      endrule;
  endruleset;

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