/*
  FMSS23 Lab 2 (Lock 2a)

  Dev note: this model keeps the "doNothing" predicate we just realized
    was needed, but switches algorithms. Instead of using flags, we're now
    using a "politeness" protocol.  

  All properties pass! great news, right!
    ...well actually...

*/

/*
  Model of a (different potential) mutual-exclusion protocol

  // run by 2 different processes (I'm blurring distinction w/ threads)
  while(true) {
    polite = this
    while(polite == this) {}
    write_to_memory() // take our turn (not modeled)
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

-- location of processes in the algorithm
abstract sig Location {}
one sig Disinterested, Waiting, InCS extends Location {}

-- two processes in the world:
abstract sig Process {
    var loc: one Location -- the process' location in the program
}
one sig ProcessA, ProcessB extends Process {}

-- model the global variable for who the polite process is
one sig Global {
    var polite: lone Process
}

---------------------------------------------------------------------
-- System model
---------------------------------------------------------------------

-----------------------------------------
-- Is the current state an initial state?
pred init {
    all p: Process | { 
        p.loc = Disinterested
    }
    no polite
}

---------------------------------------------------------------------
-- Is the process `p` allowed to execute `polite = this`?
pred waveEnabled[p: Process] {
    p.loc = Disinterested     -- `p` is at the correct location
}
-- Does the process `p` execute `polite = this`?
pred wave[p: Process] {
    -- guard:
    waveEnabled[p] 
    -- action:
    p.loc' = Waiting                       -- `p` executes a line
    all p2: Process - p | p2.loc' = p2.loc -- all other processes sleep
    Global.polite' = p                     -- "No, you first"
}

---------------------------------------------------------------------
-- Is the process `p` allowed to progress past `while(polite == this) {}`?
pred enterEnabled[p: Process] {
    Global.polite' != p
    p.loc = Waiting
}
-- Does the process `p` progress past `while(other.flag == true) {}`?
pred enter[p: Process] {
    enterEnabled[p]
    p.loc' = InCS
    all p2: Process - p | p2.loc' = p2.loc
    polite' = polite
}

---------------------------------------------------------------------
-- Is the process `p` allowed to exit the critical section and return to
--   the start of the loop?
pred leaveEnabled[p: Process] {
    p.loc = InCS
}
-- Does the process `p` exit the critical section?
pred leave[p: Process] { 
    leaveEnabled[p]
    p.loc' = Disinterested
    all p2: Process - p | p2.loc' = p2.loc
    polite' = polite -- no change in the polite variable
}

-----------------------
-- Are all processes unable to progress? 
pred doNothingEnabled {
    all p: Process | {
      not waveEnabled[p]
      not enterEnabled[p]
      not leaveEnabled[p]
    }
}
-- If so, then the system as a whole can "progress" with no change:
pred doNothing {
    doNothingEnabled
    polite' = polite
    loc' = loc
}

-----------------------
-- Transition predicate
pred delta {
    some p: Process | {
        wave[p] or
        enter[p] or
        leave[p]
	} or {
    	doNothing
	}
}

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
-- DEV note: this should now fail (in lock1b) because of doNothing.
--   Need to underscore diff between e.g. `enter` and `enterEnabled`.
--   Need to underscore that we _don't_ add doNothing here.
pred noDeadlocks {
	always some p: Process | {
		waveEnabled[p] or 
        enterEnabled[p] or 
        leaveEnabled[p]
    }
}
check checkNoDeadlocks {
    (init and always delta) implies noDeadlocks
}


-- Non-starvation property
pred nonStarvation {
    all p: Process | {
    	always { 
        	-- without a flag, we can still look at the location
            p.loc = Waiting implies eventually (p.loc = InCS)
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

