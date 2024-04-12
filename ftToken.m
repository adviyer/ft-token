
-- 3-hop MSI Protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  VC0: 0;                -- Requests
  VC1: 1;                -- Fwd/Inv
  VC2: 2;                -- Ack/Data
  QMax: 2;
  NumVCs: VC2 - VC0 + 1;
  NetMax: ProcCount+1;
  -- TBD: Change this
  Bound: 10;
  MaxSerialId: 40;
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
    Proc: scalarset(ProcCount);   -- unordered range of processors
    Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
    Token: scalarset(ProcCount); -- tokens
    Home: enum {HomeType};      -- need enumeration for IsMember calls
    Node: union {Home, Proc};

    VCType: VC0..NumVCs-1;
    AckCountType: 0..ProcCount;
    TokenCount: 0..ProcCount;
    SerialType: 0..MaxSerialId;

    MessageType: enum {

        GetS, GetX, Putt, WbAck, WbAckData, WbNack, Inv, Ack, Data, DataEx,
        Unblock, UnblockEx, AckO, AckBd, UnblockPing,
        WbPing, WbCancel, OwnerPing, NackO

    };

    Message:
        Record
            /*
             * do not need a destination for verification;
             * the destination is indicated by which array
             * entry in the Net the message is placed
             */
            mtype: MessageType;
            src: Node;
            vc: VCType;
            val: Value;
            numAcks: AckCountType;
            numToken: TokenCount;
            hasOwnerToken: boolean;
            hasBackupToken: boolean;
            serialId: SerialType;
        End;

    HomeState:
        Record
            state: enum {
                -- TBD: Fill this
            };
            owner: Node;
            sharers: multiset [ProcCount] of Node;
            val: Value; 
        End;

    ProcState:
        Record
            state: enum {
                -- TBD: Fill this
            };
            val: Value;
            acks: AckCountType;
            acksGot: AckCountType;
            numTokens: TokenCount;
            hasOwnerToken: boolean;
            hasBackupToken: boolean;
        End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
    MainMem:  HomeState;
    Procs: array [Proc] of ProcState;
    Net:   array [Node] of multiset [NetMax] of Message;  -- One multiset for each destination - messages are arbitrarily reordered by the multiset
    InBox: array [Node] of array [VCType] of Message; -- If a message is not processed, it is placed in InBox, blocking that virtual channel
    msg_processed: boolean;
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
    numAcks: AckCountType;
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
    MultiSetAdd(msg, Net[dst]);
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
  choose midx: Net[n] do
    alias chan: Net[n] do
    alias msg: chan[midx] do
    alias box: InBox[n] do

    -- Pick a random message in the network and delivier it
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
    Procs[n].numTokens = ProcCount & Procs[n].hasOwnerToken = true
  end;

invariant "Read Rule"
  Forall n : Proc Do  
    Procs[n].state = P_S
    ->
    Procs[n].numTokens >= 1 & Procs[n].hasOwnerToken = false
  end;

invariant "Valid-Data Bit Rule"
  Forall n : Proc Do  
    Procs[n].numTokens = 0 | (Procs[n].numTokens = 1 & Procs[n].hasBackupToken)
    ->
    isundefined(Procs[n].val)
  end;
