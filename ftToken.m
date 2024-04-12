
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
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
    Proc: scalarset(ProcCount);   -- unordered range of processors
    Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
    Home: enum { HomeType };      -- need enumeration for IsMember calls
    Node: union { Home , Proc };

    VCType: VC0..NumVCs-1;
    AckCountType: 0..ProcCount;

    MessageType: enum {

        GetS, GetM, PutS, PutM, PutMS, PutE, Inv,    -- VC0
        FwdGetS, FwdGetM,                            -- VC1
        PutAck, PutAckI, PutAckGet, InvAck,          -- VC2
        Data, DataP, DataE                -- VC2

    };

    Message:
        Record
            mtype: MessageType;
            src: Node;
            -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
            vc: VCType;
            val: Value;
            numAcks: AckCountType;
        End;

    HomeState:
        Record
            state: enum {
                H_M, H_S, H_I, H_E, -- Stable states for MSI
                H_Sd, H_Sp          -- Intermediate waiting for data
            };
            owner: Node;  
            sharers: multiset [ProcCount] of Node;
            val: Value; 
        End;

    ProcState:
        Record
            state: enum {
                P_M, P_S, P_I, P_E,
                P_ISd, P_IMad, P_IMa,
                P_SMad, P_SMa,
                P_MIa, P_MSa, P_SIa, P_SSa, P_IIa
            };
            val: Value;
            acks: AckCountType;
            acksGot: AckCountType;
        End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
    HomeNode:  HomeState;
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
);
var msg: Message;
Begin
    if isundefined(dst) then
        put mtype; put "\n";
        put dst; put "\n";
        put src; put "\n";
    endif;
    assert !isundefined(dst) "msg dest undefined!\n";
    --assert !isundefined(src) "msg src undefined!\n";
    assert(MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
    msg.mtype   := mtype;
    msg.src     := src;
    msg.vc      := vc;
    msg.val     := val;
    msg.numAcks := numAcks;
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

Procedure AddToSharersList(n:Node);
Begin
    if MultiSetCount(i: HomeNode.sharers, HomeNode.sharers[i] = n) = 0
    then
        MultiSetAdd(n, HomeNode.sharers);
    endif;
End;

Function IsSharer(n: Node) : Boolean;
Begin
    return MultiSetCount(i: HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;

Procedure RemoveFromSharersList(n:Node);
Begin
    MultiSetRemovePred(i: HomeNode.sharers, HomeNode.sharers[i] = n);
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst: Node);
Begin
    for n: Node do
        if (IsMember(n, Proc) &
                MultiSetCount(i: HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
        then
            if n != rqst
            then 
                Send(Inv, n, rqst, VC0, undefined, undefined);
            endif;
        endif;
    endfor;
End;


Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;  -- for counting sharers
Begin

    -- Debug output may be helpful:
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put HomeNode.state;

    -- The line below is not needed in Valid/Invalid protocol.  However, the 
    -- compiler barfs if we put this inside a switch, so it is useful to
    -- pre-calculate the sharer count here
    cnt := MultiSetCount(i: HomeNode.sharers, true);


    -- default to 'processing' message.  set to false otherwise
    msg_processed := true;

    switch HomeNode.state

        case H_M:
            Assert(IsUndefined(HomeNode.owner) = false) 
                "HomeNode has no owner, but line is Modified";
            switch msg.mtype

                case GetS:
                    HomeNode.state := H_Sd;
                    if (!isundefined(HomeNode.owner)) then
                        AddToSharersList(HomeNode.owner);
                    endif;
                    AddToSharersList(msg.src);
                    Send(FwdGetS, HomeNode.owner, msg.src, VC1, undefined, undefined);

                case GetM:
                    Send(FwdGetM, HomeNode.owner, msg.src, VC1, undefined, undefined);
                    HomeNode.owner := msg.src;
                    undefine HomeNode.sharers;

                case PutS:
                    -- Happens in a store-WB race
                    -- Requesting processor should expect an Inv
                    Send(PutAckI, msg.src, HomeType, VC2, undefined, undefined);

                case PutM, PutMS:
                    if HomeNode.owner = msg.src then
                        if msg.mtype = PutMS then
                            HomeNode.state := H_S;
                            AddToSharersList(msg.src);
                        else
                            HomeNode.state := H_I;
                        endif;
                        HomeNode.val := msg.val;
                        undefine HomeNode.owner;
                        Send(PutAck, msg.src, HomeType, VC2, undefined, undefined);
                    else
                        Send(PutAckGet, msg.src, HomeType, VC2, undefined, undefined);
                    endif;

                case PutE:
                    assert HomeNode.owner != msg.src "Received PutE from owner in H_M!";
                    Send(PutAckGet, msg.src, HomeType, VC2, undefined, undefined);

                else
                    ErrorUnhandledMsg(msg, HomeType);

            endswitch;

        case H_E:
            Assert(IsUndefined(HomeNode.owner) = false) 
                "HomeNode has no owner, but line is Exclusive";
            switch msg.mtype

                case GetS:
                    HomeNode.state := H_Sd;
                    AddToSharersList(HomeNode.owner);
                    AddToSharersList(msg.src);
                    Send(FwdGetS, HomeNode.owner, msg.src, VC1, undefined, undefined);

                case GetM:
                    Send(FwdGetM, HomeNode.owner, msg.src, VC1, undefined, undefined);
                    HomeNode.owner := msg.src;
                    HomeNode.state := H_M;
                    undefine HomeNode.sharers;

                case PutS:
                    -- Happens in a store-WB race
                    -- Requesting processor should expect an Inv
                    Send(PutAckI, msg.src, HomeType, VC2, undefined, undefined);

                case PutM, PutMS, PutE:
                    if HomeNode.owner = msg.src then
                        if msg.mtype = PutMS then
                            HomeNode.state := H_S;
                            AddToSharersList(msg.src);
                        else
                            HomeNode.state := H_I;
                        endif;
                        if msg.mtype != PutE then
                            HomeNode.val := msg.val;
                        endif;
                        undefine HomeNode.owner;
                        Send(PutAck, msg.src, HomeType, VC2, undefined, undefined);
                    else
                        Send(PutAckGet, msg.src, HomeType, VC2, undefined, undefined);
                    endif;

                else
                    ErrorUnhandledMsg(msg, HomeType);

            endswitch;

        case H_S:
            switch msg.mtype

                case GetS:
                    AddToSharersList(msg.src);
                    Send(Data, msg.src, HomeType, VC2, HomeNode.val, undefined);

                case GetM:
                    HomeNode.state := H_M;
                    SendInvReqToSharers(msg.src);
                    if (IsSharer(msg.src)) then
                        cnt := cnt - 1;
                    endif;
                    Send(Data, msg.src, HomeType, VC2, HomeNode.val, cnt);
                    HomeNode.owner := msg.src;
                    undefine HomeNode.sharers;

                case PutS:
                    if cnt = 1 & IsSharer(msg.src) then
                        HomeNode.state := H_I;
                        undefine HomeNode.owner;
                        undefine HomeNode.sharers;
                    else
                        RemoveFromSharersList(msg.src);
                    endif;
                    Send(PutAck, msg.src, HomeType, VC2, undefined, undefined);

                case PutM, PutMS, PutE:
                    -- Can happen for race b/w PutM and FwdGetS
                    if msg.mtype != PutMS then
                        RemoveFromSharersList(msg.src);
                    endif;
                    Send(PutAck, msg.src, HomeType, VC2, undefined, undefined);

                else
                    ErrorUnhandledMsg(msg, HomeType);


            endswitch;

        case H_I:
            switch msg.mtype

                case GetS:
                    HomeNode.state := H_E;
                    Send(DataE, msg.src, HomeType, VC2, HomeNode.val, undefined);
                    HomeNode.owner := msg.src;

                case GetM:
                    HomeNode.state := H_M;
                    Send(Data, msg.src, HomeType, VC2, HomeNode.val, 0);
                    HomeNode.owner := msg.src;
                    undefine HomeNode.sharers;
                    undefine HomeNode.val;
                
                case PutS, PutM, PutMS, PutE:
                    Send(PutAck, msg.src, HomeType, VC2, undefined, undefined);

                else
                    ErrorUnhandledMsg(msg, HomeType);

            endswitch;

        case H_Sd:
            switch msg.mtype

                case GetS:
                    msg_processed := false;

                case GetM:
                    msg_processed := false;

                case PutS:
                    if (IsSharer(msg.src)) then
                        Send(PutAck, msg.src, HomeType, VC2, undefined, undefined);
                    else
                        Send(PutAckI, msg.src, HomeType, VC2, undefined, undefined);
                    endif;
                    RemoveFromSharersList(msg.src);

                case PutM, PutE, PutMS:
                    msg_processed := false;

                case Data:
                    HomeNode.state := H_S;
                    HomeNode.val := msg.val;
                    HomeNode.owner := HomeType;

                case DataP:
                    HomeNode.state := H_Sp;
                    HomeNode.val := msg.val;

                else
                    ErrorUnhandledMsg(msg, HomeType);

            endswitch;

            case H_Sp:
                switch msg.mtype

                    case GetS, GetM, PutS:
                        msg_processed := false;

                    case PutM, PutE, PutMS:
                        if msg.src = HomeNode.owner then
                            HomeNode.state := H_S;
                            HomeNode.owner := HomeType;
                        endif;
                        if msg.mtype = PutMS then
                            if msg.src = HomeNode.owner then
                                AddToSharersList(msg.src);
                            endif;
                        else
                            RemoveFromSharersList(msg.src);
                        endif;
                        Send(PutAck, msg.src, HomeType, VC2, undefined, undefined);

                else
                    ErrorUnhandledMsg(msg, HomeType);

                endswitch;


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

        case P_S:
            switch msg.mtype
                case Inv:
                    Send(InvAck, msg.src, p, VC2, undefined, undefined);
                    ps := P_I;
                    undefine pv;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case P_ISd:

            switch msg.mtype
                case FwdGetS, FwdGetM, Inv:
                    msg_processed := false;
                case DataE:
                    pv := msg.val;
                    ps := P_E;
                case Data:
                    pv := msg.val;
                    ps := P_S;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case P_IMad:
            switch msg.mtype
                case FwdGetS, FwdGetM:
                    msg_processed := false;
                case Data:
                    Procs[p].acks := msg.numAcks;
                    pv := msg.val;
                    ps := P_IMa;
                    if msg.src != HomeType | Procs[p].acksGot = Procs[p].acks then
                        Procs[p].acks := 0;
                        Procs[p].acksGot := 0;
                        ps := P_M;
                    endif;
                case InvAck:
                    Procs[p].acksGot := Procs[p].acksGot + 1;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case P_SMad:
            switch msg.mtype
                case FwdGetS, FwdGetM:
                    msg_processed := false;
                case Inv:
                    -- Send InvAck to Local node
                    Send(InvAck, msg.src, p, VC2, undefined, undefined);
                    ps := P_IMad;
                case Data:
                    Procs[p].acks := msg.numAcks;
                    ps := P_SMa;
                    if msg.src != HomeType | Procs[p].acksGot = Procs[p].acks then
                        Procs[p].acks := 0;
                        Procs[p].acksGot := 0;
                        ps := P_M;
                    endif;
                case InvAck:
                    Procs[p].acksGot := Procs[p].acksGot + 1;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case P_IMa, P_SMa:
            switch msg.mtype
                case FwdGetS, FwdGetM:
                    msg_processed := false;
                case InvAck:
                    Procs[p].acksGot := Procs[p].acksGot + 1;
                    if Procs[p].acksGot = Procs[p].acks then
                        Procs[p].acks := 0;
                        Procs[p].acksGot := 0;
                        ps := P_M;
                    endif;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case P_M:
            switch msg.mtype
                case FwdGetS:
                    -- Send data to Home and Local nodes
                    Send(Data, HomeType, p, VC2, pv, undefined);
                    Send(Data, msg.src, p, VC2, pv, undefined);
                    ps := P_S;
                case FwdGetM:
                    -- Send data to Local node
                    Send(Data, msg.src, p, VC2, pv, 0);
                    ps := P_I;
                    undefine pv;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case P_E:
            switch msg.mtype
                case FwdGetS:
                    -- Send data to Home and Local nodes
                    Send(Data, HomeType, p, VC2, pv, undefined);
                    Send(Data, msg.src, p, VC2, pv, undefined);
                    ps := P_S;
                case FwdGetM:
                    -- Send data to Local node
                    Send(Data, msg.src, p, VC2, pv, 0);
                    ps := P_I;
                    undefine pv;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case P_MSa:
            switch msg.mtype
                case FwdGetS:
                    -- Send data to Home and Local nodes
                    Send(DataP, HomeType, p, VC2, pv, undefined);
                    Send(Data, msg.src, p, VC2, pv, undefined);
                    -- Just wait for PutAck
                    ps := P_SSa;
                case FwdGetM:
                    -- Send data to Local node
                    Send(Data, msg.src, p, VC2, pv, 0);
                    ps := P_IIa;
                    undefine pv;
                case Inv:
                    Send(InvAck, msg.src, p, VC2, undefined, undefined);
                    ps := P_IIa;
                    undefine pv;
                case PutAck:
                    ps := P_S;
                case PutAckGet:
                    msg_processed := false;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case P_MIa:
            switch msg.mtype
                case FwdGetS:
                    -- Send data to Home and Local nodes
                    Send(DataP, HomeType, p, VC2, pv, undefined);
                    Send(Data, msg.src, p, VC2, pv, undefined);
                    -- Behave like it was a sharer and is waiting for PutAck
                    ps := P_SIa;
                case FwdGetM:
                    -- Send data to Local node
                    Send(Data, msg.src, p, VC2, pv, 0);
                    ps := P_IIa;
                    undefine pv;
                case PutAck:
                    ps := P_I;
                    undefine pv;
                case PutAckGet:
                    msg_processed := false;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case P_SSa, P_SIa:
            switch msg.mtype
                case Inv:
                    Send(InvAck, msg.src, p, VC2, undefined, undefined);
                    ps := P_IIa;
                case PutAckI:
                    msg_processed := false; -- Stall until Inv received
                case PutAck, PutAckGet:
                    if ps = P_SSa then
                        ps := P_S;
                    else
                        ps := P_I;
                        undefine pv;
                    endif;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case P_IIa:
            switch msg.mtype
                case PutAck, PutAckI, PutAckGet:
                    ps := P_I;
                    undefine pv;
                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        else
          ErrorUnhandledState();
          
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

    rule "spontaneous-downgrade"
        (p.state = P_M)
    ==>
        Send(PutMS, HomeType, n, VC1, p.val, 0);
        p.state := P_MSa;
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
    For v: Value do
        -- home node initialization
        HomeNode.state := H_I;
        undefine HomeNode.owner;
        HomeNode.val := v;
    endfor;
    LastWrite := HomeNode.val;
    
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
  HomeNode.state = H_I
    ->
      IsUndefined(HomeNode.owner);

invariant "value in memory matches value of last write, when invalid or shared"
     HomeNode.state = H_I | HomeNode.state = H_S
    ->
      HomeNode.val = LastWrite;

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

invariant "modified implies empty sharers list"
  HomeNode.state = H_M
    ->
      MultiSetCount(i: HomeNode.sharers, true) = 0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = H_I
    ->
      MultiSetCount(i: HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do  
     HomeNode.state = H_S | HomeNode.state = H_I
    ->
      HomeNode.val = LastWrite
  end;

invariant "values in shared state match memory"
  Forall n : Proc Do  
     HomeNode.state = H_S & Procs[n].state = P_S
    ->
      HomeNode.val = Procs[n].val
  end;
