/**
  A model of a (broken) locking algorithm, which we might invent 
  on the way to the Peterson Lock:
  https://en.wikipedia.org/wiki/Peterson%27s_algorithm

  Informal: There are two threads (A and B) executing concurrently, 
  each running an arbitrary program. These threads sometimes need 
  access to a shared resource -- such as a memory location -- but 
  only one thread should be allowed access at a time. The portion 
  of each program that uses the shared resource is called the 
  "critical section".

  Semiformal description of actions:

  The DOMAIN consists of the two threads running their programs.
  It executes the following actions (where 'id' is either A or B):

	- enterCS[id]  (not visible to the system):
      enter the critical section (start accessing the shared resource)
    
	- exitCS[id]  (not visible to the system): 
      exit the critical section (done with the shared resource)
    
	- requestAccess[id]  (visible to the system):
      request access from the locking system

	- withdrawRequest[id]  (visible to the system):
      withdraw request for access from the locking system

  Note that none of these actions are specific to a particular kind
  of locking system, beyond a general notion of requesting access etc. 
  Moreover, because entering/exiting are separate from requesting/withdrawing,
  we can represent "good behavior" from the threads (e.g., not accessing the 
  resource unless authorized) as optional domain knowledge, rather than
  assuming it implicitly in the model.


  The SYSTEM is the locking algorithm that controls access to the shared
  resource. It executes the following actions (where 'id' is either A or B):
  
	- grantAccessTo[id]:
    signal to the thread that it may enter its critical section and
    access the shared resource.

  A more high-fidelity model would consider the scheduler, etc. but it's
  not necessary to include those lower-level details for the moment.

*/

/********************************************************************
* Datatypes
********************************************************************/

-- Domain
abstract sig Thread {
  var state: one ThreadState
}
one sig A, B extends Thread {}
abstract sig ThreadState {} 
one sig Uninterested, Waiting, InCS, Finished extends ThreadState {}

-- System
one sig Lock {
  -- NOTE: silent failure (unsat) if try to refer to flags' without
  -- the var annotation; that should really produce a warning in Alloy...

  -- Active request noted by system
  var flags: set Thread,
  -- System has currently granted access
  var granted: set Thread
}

/********************************************************************
* Domain-controlled actions
********************************************************************/

-- Frame-condition helper: all _other_ threads' state is unchanged
pred othersSame[t: Thread] { 
	all t2: Thread - t |  t2 in Lock.flags' iff t2 in Lock.flags
	all t2: Thread - t |  t2 in Lock.granted' iff t2 in Lock.granted
	all t2: Thread - t |  t2.state' = t2.state
}

-- The enterCS and exitCS actions are not observable by the system, 
-- and so all we can specify about them without domain knowledge
-- is that they don't change the system's state. We will, however,
-- assume a certain amount of good behavior, enforced by preconditions
-- on the domain variable 'state'

-- Analogy: "people waiting on floor X" from 4DC paper
pred enterCS[t: Thread] {
  t.state = Waiting                    -- GUARD (domain)
  t in Lock.granted                    -- GUARD (system interface var)
  t.state' = InCS                      -- EFFECT (domain)
  t in Lock.flags' iff t in Lock.flags -- FRAME
  t in Lock.granted' iff t in Lock.granted -- FRAME
  othersSame[t]                        -- FRAME
}
pred exitCS[t: Thread] {
  t.state = InCS                       -- GUARD (domain)
  t.state' = Finished                  -- EFFECT (domain)
  t in Lock.flags' iff t in Lock.flags -- FRAME
  t in Lock.granted' iff t in Lock.granted -- FRAME
  othersSame[t]                        -- FRAME
}

-- These are observable by the system, and can result in a change in 
-- the flags variable.
--    Analogy: "someone presses the button on floor X" from 4DC paper
pred requestAccess[t: Thread] {
   t.state = Uninterested               -- GUARD (domain)
   t.state' = Waiting                   -- EFFECT (domain)
   t in Lock.flags'                     -- EFFECT (system)
   othersSame[t]                        -- FRAME
   t in Lock.granted' iff t in Lock.granted -- FRAME
}

pred withdrawRequest[t: Thread] {
   t.state = Finished                   -- GUARD (domain)
   t.state' = Uninterested              -- EFFECT (domain)
   t not in Lock.flags'                 -- EFFECT (system)
   t not in Lock.granted'               -- EFFECT (system interface var)
   othersSame[t]                        -- FRAME
}

/********************************************************************
* System-controlled actions
*   Since the system controls these actions, our specification 
*   of the system contols when they can be performed.
********************************************************************/

pred grantAccessTo_Enabled[t: Thread] {
   -- NOTE WELL: The system cannot observe t.state!
   -- Instead, it will read shared interface variable
   t in Lock.flags         -- flag is raised
   t not in Lock.granted   -- access not yet granted
   all t2: Thread - t | t2 not in Lock.flags
}
pred grantAccessTo[t: Thread] {
   grantAccessTo_Enabled[t] -- GUARD
   t in Lock.granted'       -- EFFECT
   Lock.flags' = Lock.flags -- FRAME
   all t: Thread | t.state' = t.state -- FRAME
   othersSame[t]            -- FRAME
}

/********************************************************************
* Transition system
********************************************************************/

pred initialState {
   all t: Thread | t not in Lock.flags    -- SYSTEM
   all t: Thread | t not in Lock.granted    -- SYSTEM
   all t: Thread | t.state = Uninterested -- DOMAIN
}

pred someTrace {
  initialState 

  always { 
    some t: Thread | {
      -- controlled by domain (not visible to system)
      enterCS[t] or exitCS[t] or
      -- controlled by domain (visible to system)
      requestAccess[t] or withdrawRequest[t] or 
      -- controlled by system (visible to domain)
      grantAccessTo[t] 
    }
  }
}

/********************************************************************
* Requirements
********************************************************************/

-- Note that these do require some domain knowledge (e.g., connecting the
-- grantAccessTo and enterCS actions). At the moment, the model has this baked
-- into the guards of the domain actions. 
assert require_mutualExclusion {
  { someTrace } 
  implies

    all disj t, t2: Thread | { 
      always {
	    enterCS[t] implies (not enterCS[t2] until exitCS[t])
      } } }
check require_mutualExclusion

assert require_nonStarvation {
  { someTrace } 
  implies

    all t: Thread | {
      always { 
	    requestAccess[t] implies eventually enterCS[t]
    } } }
check require_nonStarvation


/********************************************************************
* Basic sanity checks
********************************************************************/

-- Can each action occur at some point?
run consistent_requestAccess {
  someTrace and eventually { some t: Thread | requestAccess[t]}
} expect 1
run consistent_withdrawRequest {
  someTrace and eventually { some t: Thread | withdrawRequest[t]}
} expect 1
run consistent_grantAccessTo {
  someTrace and eventually { some t: Thread | grantAccessTo[t]}
} expect 1
run consistent_enterCS {
  someTrace and eventually { some t: Thread | enterCS[t]}
} expect 1
run consistent_exitCS {
  someTrace and eventually { some t: Thread | exitCS[t]}
} expect 1

-- Can we witness a full execution cycle for some thread?
run consistent_one_full_cycle {
  someTrace
  some t: Thread | eventually { 
	requestAccess[t] 
    eventually {
	  grantAccessTo[t]
      eventually {
		enterCS[t]
        eventually {
		  exitCS[t]
          eventually {
			withdrawRequest[t]
          }
	    }

      }
    }
  }  
} expect 1

-- Can a thread request access multiple times? (The 'after' operator
-- is needed because 'eventually' will include the current time.)
run consistent_multipleRequestAccess {
  someTrace and some t: Thread | eventually { 
    requestAccess[t] and after eventually requestAccess[t]}
} expect 1

-- Can both threads be granted access at some point?
run consistent_multipleThreadsGrantedAccess {
  someTrace and all t: Thread | eventually {grantAccessTo[t]}
} expect 1

-- Can the system ever support a trace observing non-starvation: 
-- both threads are always eventually able to access the resource
-- NOTE WELL: this is not the same as *verifying* non-starvation!
run consistent_NonStarvation {
  someTrace and all t: Thread | eventually {grantAccessTo[t]}
} expect 1



/********************************************************************
* Domain knowledge
*   These should not constrain the behavior or timing of grant, or 
*   reference the 'flags' variable. Some are (hopefully) a consequence
*   of how we wrote the guards of the domain actions.
********************************************************************/

-- Once a thread requests, it won't request again until its request
-- with the critical section. This also implies that threads won't 
-- withdraw their requests early.
pred dk_request_once {
  all t: Thread | {
    always { 
        -- Note: TN (after, releases)
		requestAccess[t] implies 
			after {grantAccessTo[t] releases not requestAccess[t]}
    }
  }
}

-- A thread won't request access again if it has already been granted
-- for its most recent request
pred dk_no_request_if_already_granted {
  all t: Thread | 
    always {
      grantAccessTo[t] implies after {exitCS[t] releases not requestAccess[t]}
    }
}

-- Threads won't enter the critical section unless it has an active grant
-- Threads won't exit the critical section before entering
--   (Convenient to use past-time LTL)
pred dk_good_behavior {
  all t: Thread | 
    always {
      -- entering means that there was a grant in the past, with 
      -- no intervening enter
      enterCS[t] implies before {not enterCS[t] since grantAccessTo[t]}

      -- If exiting, entered some time in past without any intervening exit
      -- "Before" is "in the previous state"
      exitCS[t] implies before {not exitCS[t] since enterCS[t]}
    }
}

-- Confirm that these 3 domain-knowledge predicates are entailed by the action guards
assert assert_dk_request_once {
  someTrace implies dk_request_once}
check assert_dk_request_once
assert assert_dk_no_request_if_already_granted {
  someTrace implies dk_no_request_if_already_granted}
check assert_dk_no_request_if_already_granted
assert assert_dk_good_behavior {
  someTrace implies dk_good_behavior}
check assert_dk_good_behavior


/********************************************************************
* Optional behavioral predicates
*    These can see the flags
*    These should not constrain the behavior or timing of any action 
*      but grant. However, they may reference domain-controlled actions 
*      (e.g., in the antecedents of implication)
********************************************************************/

-- The system's flags are raised for every thread at some point
--   **without anyone being granted access at that time**
pred behavior_shared_interest_flags {
  eventually {
    Lock.flags = Thread
    no Lock.granted
  }
} 
run consistent_shared_interest_flags {
  someTrace and behavior_shared_interest_flags
} expect 1
