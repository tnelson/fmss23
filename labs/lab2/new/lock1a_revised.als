/*-------------------------------------------------------------------------
AN EXPERIMENT IN DOMAIN/SYSTEM SEPARATION  (in temporal Alloy, this time)

This is my attempt to refactor the original lock1 model in a way consistent
with the meta-modeling strategy we discussed. 

Recall the proof obligation: (D /\ S) => R
That is, our top-level goal is to show that the requirements are met by the
  specification (perhaps assuming some domain knowledge). But we are human,
  and often make mistakes. So how can we validate this model?  

  Knowing the difference between D, S, and R will help us get started.


Notes:
  * I've tried to unify syntax somewhat (e.g., using t" rather than t2)
  * I switched to the boolean library for clarity
  * More importantly, this time I chose to model the "doNothing" transition 
    more narrowly -- it is parameterized by a Thread, and renamed to 
    "waitForAccess" (invoked by the system). This removed a question that was
    troubling me about the former version: 
       "Is doNothing invoked by the system, or the domain?" 
    When I tried to answer that, I kept getting tangled with the idea of a scheduler.
    
    Moreover, this removes the motivation of `doNothing` existing only as a patch 
    semantics for the tool's semantics, which is important because...
    
  * Finally, I'll note something about the "tool focused" perspective I tend to take.
      When I noticed the issue in the original model, my reaction was: "Oh, RIGHT, 
      Alloy 6 only finds infinite traces." I blamed the problem on me forgetting 
      something about the _tool_. But I wrote a specification using the `always`
      operator. When I used `always`, I was (implicitly) invoking the infinite-trace 
      semantics of LTL. So was the thing I forgot _really_ the shape of instances
      that Alloy finds, or was it (embarrassingly) the meaning of what I had written?

      I now think it was the latter. 

-------------------------------------------------------------------------*/


-------------------------------------------------------------------------
-- DATA TYPES
-------------------------------------------------------------------------
open util/boolean

abstract sig ThreadState {}
-- These specific thread states come from the locking system, since locations 
-- in the control program may (and will) vary across different locking systems.
one sig Uninterested, Waiting, InCS extends ThreadState {}

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Interface Variables:
--   * the program location of each thread
--   * the flag variables for each thread 
---------------------------------------------------------------------

abstract sig Thread {
   var state: one ThreadState,  -- State of this thread in the system
   var flag:  one Bool          -- Does the thread have its flag raised?
}
-- There are only two threads in the domain model, at present
one sig ThreadA, ThreadB extends Thread {}

-------------------------------------------------------------------------
-- Specification (of a transition system, NOT to be confused with the 
--   system being modeled).
-------------------------------------------------------------------------*/

-- Not to be confused with a ThreadState! An initial state of the transition system
--   must have all threads Uninterested and with their flags lowered.
pred initialState {
   all t: Thread | t.state = Uninterested and t.flag = False 
}

---------------------------------------------------------------------
-- Domain actions: 
--   * requestAccess is executed by the domain 
--     (a thread may express interest even without the system)
--   * withdrawRequest is executed by the domain 
--     (a thread may withdraw its interest even without the system)
--
-- System actions:
--   * grantAccess is executed by the system 
--     (it is the system that governs when and if access will be given)
---------------------------------------------------------------------

-- Frame-condition helper: all _other_ threads' state is unchanged
pred othersSame[t: Thread] { 
	all t": Thread - t | t".state' = t".state && t".flag' = t".flag }

---------------------------------------------------------------------
-- ACTION: The thread requests access (invoked by domain)
pred requestAccess_Enabled[t: Thread] {  t.state = Uninterested  }
pred requestAccess[t: Thread] {
   requestAccess_Enabled[t] -- GUARD
   t.state' = Waiting       -- EFFECT
   t.flag' = True           
   othersSame[t]            -- FRAME
}

---------------------------------------------------------------------
-- ACTION: The thread's request is granted (invoked by locking system, executed by the thread)
pred grantAccess_Enabled[t: Thread] {
   t.state = Waiting 
   all t": Thread - t | t".flag = False
}
pred grantAccess[t: Thread] {
   grantAccess_Enabled[t] -- GUARD
   t.state' = InCS        -- EFFECT
   t.flag' = t.flag       -- FRAME
   othersSame[t]          
}

---------------------------------------------------------------------
-- ACTION: The thread has finished its request for access (invoked by domain)
--   Note how much a name matters: 
--     * "withdrawRequest" sounds like the thread can cease interest at any time,
--       in which case the Enabled predicate is too strong. In that case, we would
--       need to write our liveness requirement(s) more carefully.
--     * "finishedRequest" is far more reasonable if we want it only to be executable
--       if the thread has indeed accessed the critical section.
pred finishRequest_Enabled[t: Thread] {  t.state = InCS }
pred finishRequest[t: Thread] { 
   finishRequest_Enabled[t]  -- GUARD
   t.state' = Uninterested     -- EFFECT
   t.flag' = False
   othersSame[t]               -- FRAME
}

---------------------------------------------------------------------
-- ACTION: The thread busy-waits (invoked by the system, executed by the thread)
--   (to be used in the fixed version)
pred waitForAccess_Enabled [t: Thread] {  t.state = Waiting  }
pred waitForAccess[t: Thread] { 
   waitForAccess_Enabled[t] -- GUARD
   t.state' = Uninterested  -- EFFECT
   t.flag' = False
   othersSame[t]            -- FRAME
}

-------------------------------------------------------------------------
-- Different delta functions for different versions of this lock
-------------------------------------------------------------------------

-- The original delta function (Lock 1A)
pred lock1a_Delta_t[t: Thread] {
      requestAccess[t] or
      grantAccess[t] or
      finishRequest[t]
}
pred lock1a_Delta {
   some t: Thread | {
	 lock1a_Delta_t[t]
   }
}
run lock1a_anyTrace {  
   initialState 
   always lock1a_Delta  
} expect 1

-------------------------------------------------------------------------
-- The modified delta function (Lock 1B), for comparison
pred lock1b_Delta {
   some t: Thread | {
      requestAccess[t] or
      grantAccess[t] or
      waitForAccess[t] or
      finishRequest[t] 
   }
}

run lock1b_anyTrace {  
   initialState 
   always lock1b_Delta  
} expect 1


-------------------------------------------------------------------------
-- Requirements 
--   "How we wish the domain to behave in the presence of the system"
-------------------------------------------------------------------------


---------------------------------------------------------------------
-- REQUIREMENT: Mutual Exclusion (multiple formulations)
---------------------------------------------------------------------

-- Formulation entirely in terms of actions
-- If one thread is granted access, then the other must not be granted access
--  until the first's request is finished. Requires Until LTL operator.
pred require_mutualExclusion_via_actions {
    all disj t, t": Thread | { 
      always {
	    grantAccess[t] => (not grantAccess[t"] until finishRequest[t])
      } } }

-- Formulation using ThreadState (thread states are part of the interface)
pred require_mutualExclusion_via_state {
    all disj t, t": Thread | { 
      always {   
		t.state != InCS or t".state != InCS
    } } } 

---------------------------------------------------------------------
-- REQUIREMENT: Non-starvation (liveness)
--   I am not separating out deadlock-freedom in this model, since 
--   liveness ought to imply deadlock-freedom (this is a worthwhile
--   validation check!), and liveness is what we really want. But also,
--   note that we could not phrase the property as "some action is always
--   enabled" anymore; by definition, some action _is_ always enabled in
--   a trace satisfying the specification we wrote.

-- There are multiple formulations here, too. But which is best?
---------------------------------------------------------------------

-- Formulation using only actions
pred require_nonStarvation_via_actions {
    all t: Thread | {
      always { 
	    requestAccess[t] => eventually grantAccess[t]
    } } }


-- A prospective formulation using thread states instead
pred require_nonStarvation_via_thread_states {
    all t: Thread | {
      always { 
	    t.state = Waiting => eventually t.state = InCS
    } } }

-- A prospective formulation using the flag variable for the antecedent
--   (In the full Peterson lock model, where we expect liveness to hold, 
--    this formulation may not hold if threads may remain Uninterested, 
--    since the flag is raised even while the process is in the critical 
--    section. That issue will not arise here in Lock 1.
pred require_nonStarvation_via_flag {
    all t: Thread | {
      always { 
	    t.flag = True => eventually t.state = InCS
    } } }

-------------------------------------------------------------------------
-- Validating Requirements: (D /\ S) => R
--   Only using one formulation each, for now.
-------------------------------------------------------------------------

-- Check for the first system (Lock 1A)
check requireMutualExclusion_lock1a { 
   (initialState and always lock1a_Delta) implies require_mutualExclusion_via_actions
}

-- Check for the second system (Lock 1B)
check requireMutualExclusion_lock1b { 
   (initialState and always lock1a_Delta) implies require_mutualExclusion_via_actions
}

-- Check for the second system (Lock 1A)
check requireNonStarvation_lock1a { 
   (initialState and always lock1a_Delta) implies require_nonStarvation_via_thread_states
}

-- Check for the second system (Lock 1B)
check requireNonStarvation_lock1b { 
   (initialState and always lock1b_Delta) implies require_nonStarvation_via_thread_states
}

-------------------------------------------------------------------------
-- Model Validation   (involves S and/or D, but never R)
--   Note that, by separating the specification from the domain,
--   we can restrict the scope of each of the following predicates.
--   Ask: "Is this concept I wish to check...
--     - about the domain; or
--     - about the specification?"
-------------------------------------------------------------------------


-------------------------------------------------------------------------
-- Domain-specific predicates (optional domain knowledge) 
-------------------------------------------------------------------------

-- Note that the actions themselves are optional predicates. Here:
--   finishRequest[t] 
--   requestAccess[t]

-- QUESTION: How do we categorize the checks/runs themselves? 
--   The transition system being referenced by the Delta function
--   involves actions that are invoked by both the domain and system.
--   Yet this run is checking that an action invoked by the domain
--   can be performed -- and so it feels analogous to just checking an
--   optional domain-knowledge predicate by itself in a non-temporal model.

run lock1a_threadCanRequestAccess {
  initialState and always lock1a_Delta
  some t: Thread | eventually { requestAccess[t] }   
} expect 1

run lock1a_threadCanFinishRequest {
  initialState and always lock1a_Delta
  some t: Thread | eventually { finishRequest[t] }   
} expect 1

-- TODO: combinations of these

-- The domain exhibits behavior where both threads never stop contending
pred threadsContendContinuously {
  all t: Thread | always eventually requestAccess[t]
}
run traceWith_threadsContendContinuously {
  initialState and always lock1a_Delta
  threadsContendContinuously
} expect 1



-------------------------------------------------------------------------
-- Behavioral predicates (optional specification) 
-------------------------------------------------------------------------

-- Note that the actions themselves are optional predicates. Here:
--    grantAccess[t]
--    waitForAccess[t]

run lock1a_systemCanGrantAccess {
  initialState and always lock1a_Delta
  some t: Thread | eventually { grantAccess[t] }   
}

run lock1a_systemCanSayWait {
  initialState and always lock1a_Delta
  some t: Thread | eventually { waitForAccess[t] }   
}

-----------------------------------------------------------------------
-- QUESTION: is fairness optional about the domain or the specification?
--  It does seem behavioral, although if I let myself think of a scheduler
--  in the domain, it's easy to get confused. I tend to think: "add fairness
--  as domain knowledge that's necessary for the algorithm to work".
pred lock1a_enabled_t[t: Thread] {
      requestAccess_Enabled[t] or
      grantAccess_Enabled[t] or
      finishRequest_Enabled[t]
}

pred weakFairness {
	all t: Thread { 
      (eventually always lock1a_enabled_t[t]) implies 
        (always eventually lock1a_Delta_t[t])
    }
}

-----------------------------------------------------------------------

-- TODO beyond this point: enumerate categories, more example predicates


-- Check that the transition system can produce traces where both flags are raised at once)
//pred all_flags_simultaneously {
//  initialState always lock1a_Delta
//  eventually { all t: Thread | t.flag = True } 
//}
//run all_flags_simultaneously expect 1



