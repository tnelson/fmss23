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
*/

/*
  Model of a (potential) mutual-exclusion protocol

  // DEV note: "program location" or "state" or "program counter"
  // DEV note: replace "disinterested"

  // run by 2 different processes (I'm blurring distinction w/ threads)
  while(true) {
    // Location (in model only): UNINTERESTED (SATISFIED?)
    this.flag = true
    // Location (in model only): WAITING
    while(other.flag == true) { sleep(10); } // keep waiting until other.flag is false
    // Location (in model only): IN-CS
    // not shown: take our turn (write to shared memory, or something like that)
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


-- symbol for a raised flag that both processes can use
one sig Flag {} 

-- location of processes in the algorithm
abstract sig Location {}
one sig Disinterested, Waiting, InCS extends Location {}

-- two processes in the world, each of which has 2 fields
abstract sig Process {
    var loc: one Location, -- the process' location in the program
    var flag: lone Flag    -- does the process have its flag raised?
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
        p.loc = Disinterested
        no p.flag
    }
}

---------------------------------------------------------------------
-- Is the process `p` allowed to execute `this.flag = true`?
pred raiseEnabled[p: Process] {
    p.loc = Disinterested     -- `p` is at the correct location
}
-- Does the process `p` execute `this.flag = true`?
pred raise[p: Process] {
    -- guard:
    raiseEnabled[p] 
    -- action:
   
    p.loc' = Waiting                       -- `p` executes a line
    all p2: Process - p | p2.loc' = p2.loc -- all other processes sleep

    flag' = flag + (p -> Flag)             -- the line sets just one flag

	-- DEV note: (use different shapes of frame conditions as language tutorial--undersore
    --   the frame condition, and show can do them separately or not!)
}

---------------------------------------------------------------------
-- Is the process `p` allowed to progress past `while(other.flag == true) {}`?
pred enterEnabled[p: Process] {
    p->Flag = flag  -- can only advance if no other flag is raised
    p.loc = Waiting
}
-- Does the process `p` progress past `while(other.flag == true) {}`?
pred enter[p: Process] {
    enterEnabled[p]
    p.loc' = InCS
    all p2: Process - p | p2.loc' = p2.loc
    flag' = flag
}

---------------------------------------------------------------------
-- Is the process `p` allowed to execute `this.flag = false`?
pred leaveEnabled[p: Process] {
    p.loc = InCS
}
-- Does the process `p` execute `this.flag = false`?
pred leave[p: Process] { 
    leaveEnabled[p]
    p.loc' = Disinterested
    all p2: Process - p | p2.loc' = p2.loc
    flag' = flag - (p->Flag)
}

-----------------------
-- Transition predicate
pred delta {
    some p: Process | {
        raise[p] or
        enter[p] or
        leave[p]
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
    always #{p: Process | p.loc = InCS} <= 1
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
        leaveEnabled[p]
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
			-- DEV note: this will need changing in next model
            some p.flag implies eventually (p.loc = InCS)
        }
    }
}
check checkNonStarvation {
    (init and always delta) implies nonStarvation
}

---------------------------------------------------------------------
-- Validation
---------------------------------------------------------------------

-- DEV note: should add discussion of what is missing (ask them to write one?

run vacuityCheck {
    init
    always delta
} expect 1

run bothFlagsSimultaneously {
    init
    always delta
    eventually {
        -- note: beware precedence; we need the { ... } here
	    some ProcessA.flag and some ProcessB.flag
    }
} expect 1


