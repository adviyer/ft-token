
-- Fault-tolerant token coherence protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  MaxNum: 1
  
----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
    NumType: 0..MaxNum;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
    num: NumType;

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------


----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)

rule "zero rule"
  (num = 0)
==>
  num := 1;
endrule;


rule "one rule"
  (num = 1)
==>
  num := 0;
endrule;


----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate
    
    num := 0;
    
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Maximum of one owned token"
    num < 2;


