/*
  FMSS23 Lab 2 (Lock 1a)

  Dev note: This is the first model students will work with. It 
    introduces the basic structure we'll use, along with 3 properties:
      - mutual exclusion
      - non-deadlock
      - non-starvation
    This model shows all properties passing! Good news, right? :-)
    Well, unfortunately not. The model doesn't admit deadlocks because 
    of how Alloy6 works.

    Link OOPS to Jackson-Zave model and validation:
      - Shapes of traces from the domain are not supported by the _tool_. This manifests as
        a weak domain model (i.e., it would affect _any_ system we modeled in Alloy 6.)
      - I don't believe this issue is something we can discover with (D /\ S) => R;
        rather, D (model of how the domain behaves by itself) is too restrictive and 
        thus covers up the weakness in S (how the system behaves at the interface).
    Link OOPS to techniques from lecture:
      - Take idea from lecture 1: predicates. "Optional properties"; need only be true
        of one trace (but must be true of SOME trace!)   
      - Write some predicates and run them, checking for vacuity etc.?
        (WE know that the domain model is wrong because we can see the deadlock. But 
         let's pretend this was a bigger model, and harder to comprehend.)

   Flow of lab:
     [15min] LTL in Alloy 6, sketch transition system
     [5min] Paired exercise: run; do you believe this algorithm?
     [5min] Together: any concerns? 
            (Expect that they say some properties should not be 
             passing; if not, can step through drawing the DFA.)
     [2.5min] Paired exercise: where does this issue fit into Jackson-Zave?
     [2.5min] Together: discuss (if we seek (D /\ S) => R, then a 
            restrictive domain model may make S look sufficient for R.)            
     [15min] Paired exercise: follow Lecture 1 advice, run predicates.
             (But note these don't always need to be predicates about S.)
     [5min] Together: discuss, show predicate vs. deliberate deadlock.
     ----------  (50 min total for lock1a)
     [10min] Livecode lockb -- explicit stutter transition, validate!
     ----------  (60 min total for lock1a+lock1b)
     [10min] Together: sketch and explore lock2, motivate
     [5min] Paired exercise: run; do you believe *this* algorithm?
     [15min] Validation! And notice issue... 
     ----------  (90 min total; no room for Peterson)
      ^ Slightly too long, but within reasonable range for trimming
       Can find 10-15 min to remove.
*/

/*
  Pseudocode for a (potential) mutual-exclusion protocol, which we
  will be modeling:

  // run by 2 different processes (I'm blurring distinction w/ threads)
  while(true) {
    // ProgramLocation (in model only): UNINTERESTED 
    this.flag = true
    // ProgramLocation (in model only): WAITING
    while(other.flag == true) { sleep(10); } // keep waiting until other.flag is false
    // ProgramLocation (in model only): IN-CS
	doSomethingWithMemory();
    this.flag = false
  }

  What do we _want_ from the protocol? Some goals might be:
    - mutual exclusion: at most one thread is in the 
      critical-section at any time
    - no deadlocks: SOME thread can progress at any given time
    - non-starvation: if i'm interested, i get to go eventually
*/

---------------------------------------------------------------------
-- Sig and field definitions
---------------------------------------------------------------------
open util/boolean

-- location of processes in the algorithm; we don't call this "state"
--  to avoid confusion vs. the overall state of the system.
abstract sig ProgramLocation {}
one sig Uninterested, Waiting, InCS extends ProgramLocation {}

-- two processes in the world, each of which has 2 fields
abstract sig Process {
    var progloc: one ProgramLocation, -- the process' location in the program
    var flag: one Bool                -- does the process have its flag raised?
}
one sig ProcessA, ProcessB extends Process {}


---------------------------------------------------------------------
-- System model
---------------------------------------------------------------------

-- Note re: temporal Alloy:
--   formulas are evaluated with respect to some state index. E.g.,
--   init: "the first state is initial"
--   next_state init: "the second state is initial"

-----------------------------------------
-- Is the current state an initial state?
pred init {
    all p: Process | { 
        p.progloc = Uninterested
        p.flag = False
    }
}

---------------------------------------------------------------------
-- Is the process `p` allowed to execute `this.flag = true`?
pred raiseEnabled[p: Process] {
    p.progloc = Uninterested     -- `p` is at the correct location
}
-- Does the process `p` execute `this.flag = true`?
pred raise[p: Process] {
    -- guard:
    raiseEnabled[p] 
    -- action:
   
    p.progloc' = Waiting                       -- `p` executes a line
    all p2: Process - p | p2.progloc' = p2.progloc -- all other processes sleep

    flag' = flag ++ (p -> True)            

	-- DEV note: (use different shapes of frame conditions as language tutorial--undersore
    --   the frame condition, and show can do them separately or not!)
}

---------------------------------------------------------------------
-- Is the process `p` allowed to progress past `while(other.flag == true) {}`?
pred enterEnabled[p: Process] {
    flag.True = p  -- can only advance if no other flag is raised
    p.progloc = Waiting
}
-- Does the process `p` progress past `while(other.flag == true) {}`?
pred enter[p: Process] {
    enterEnabled[p]
    p.progloc' = InCS
    all p2: Process - p | p2.progloc' = p2.progloc
    flag' = flag
}

---------------------------------------------------------------------
-- Is the process `p` allowed to execute `this.flag = false`?
pred lowerEnabled[p: Process] {
    p.progloc = InCS
}
-- Does the process `p` execute `this.flag = false`?
pred lower[p: Process] { 
    lowerEnabled[p]
    p.progloc' = Uninterested
    all p2: Process - p | p2.progloc' = p2.progloc
    flag' = flag ++ (p->False) -- update
}

-----------------------
-- Transition predicate
pred delta {
    some p: Process | {
        raise[p] or
        enter[p] or
        lower[p]
	}
}

-- Example: generate a trace this way:
pred findATrace {
  init
  always delta
}
-- an instance of a model in Alloy 6 is a single trace
run findATrace


---------------------------------------------------------------------
-- Properties and property checking
---------------------------------------------------------------------

-- Mutual exclusion property
pred mutualExclusion {
    always #{p: Process | p.progloc = InCS} <= 1
}
check checkMutualExclusion { 
    (init and always delta) implies mutualExclusion
}

-- No deadlock property
-- DEV note: should fail, but doesn't.
--   Need to underscore diff between e.g. `enter` and `enterEnabled`.
--   Need to discover _why_ suceeds (our transition predicate REQUIRES it!
--     that's not encouraging.)
pred noDeadlocks {
	always some p: Process | {
		raiseEnabled[p] or 
        enterEnabled[p] or 
        lowerEnabled[p]
    }
}
check checkNoDeadlocks {
    (init and always delta) implies noDeadlocks
}


-- Non-starvation property
--  Looks like it passes! (Good news, right? :-))
pred nonStarvation {
    all p: Process | {
    	always { 
        	-- interested if flag is raised
            p.flag = True implies eventually (p.progloc = InCS)
        }
    }
}
check checkNonStarvation {
    (init and always delta) implies nonStarvation
}

---------------------------------------------------------------------
-- Validation
---------------------------------------------------------------------

-- Start with the most basic predicate: "a trace of this system exists"
pred traceOfSystem {
    init
    always delta
}
run traceOfSystem expect 1

---------------------------------------------------------------
-- Let's start generating predicates, as suggested by Lecture 1
-- ...some examples, not all of which are immediately useful to 
-- the "the issue", but expect students to produce a few.
---------------------------------------------------------------

-- The system can reach a state where both flags are raised
pred reachable_BothFlagsSimultaneously {
    traceOfSystem
    eventually {
        -- note: beware precedence; we need the { ... } here
	    ProcessA.flag = True and ProcessB.flag = True
    }
} 
run reachable_BothFlagsSimultaneously expect 1

-- ...
-- But the problem isn't necessarily in "the system"!
-- Let's check the baseline. We expect a lot of bad states 
-- to be reachable. Are there any deadlock states at all
-- that can even be represented in the system model?

pred reachable_deadlock {
    eventually no p: Process | {
		raiseEnabled[p] or 
        enterEnabled[p] or 
        lowerEnabled[p]
    }
}
run reachable_deadlock expect 1

-- (The "domain" vs. "tool" distinction is delicate. I am not entirely
--  confident that it's reasonable to place this issue in the (D)omain model.

-- Yes. Is this enough?
--   (1) We know that (D /\ S) disallows deadlocks.
--   (2) We know that a deadlock state can be *represented* by the model.

-- We *don't* know whether a deadlock state can ever be reachable, 
--  even in a buggy system model.

-- Define a broken, one-transition system that must deadlock
pred broken_system {
  init -- still start in a proper initial state, but...
  
  -- deliberate contradiction 
  always { 
     some p: Process | {
        raise[p] and not raise[p]
     }
  }
}
run broken_system expect 1

-- So D can represent a deadlock state, but it cannot _reach_ such 
-- a state.


