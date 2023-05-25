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

  The DOMAIN consists of the two threads running their programs.
  It executes the following actions (where 'id' is either A or B):

	- enter[id]  (not visible to the system):
      enter the critical section (accessing the shared resource)
    
	- exit[id]  (not visible to the system): 
      exit the critical section (done with the shared resource)
    
	- request[id]  (visible to the system):
      request access from the locking system

	- withdraw[id]  (visible to the system):
      withdraw request for access from the locking system

  Note that none of these actions are specific to a particular kind
  of lock, beyond a general notion of requesting access etc. Because 
  entering/exiting is separate from requesting/withdrawing, we can
  represent "good behavior" from the threads (e.g., not accessing the 
  resource unless authorized) as optional domain knowledge, rather than
  assuming it implicitly in the model.


  The SYSTEM is the locking algorithm that controls access to the shared
  resource. It executes the following actions (where 'id' is either A or B):
  
	- grant[id]:
    signal to the thread that it may enter its critical section and
    access the shared resource.

  A more high-fidelity model would consider the scheduler, etc. but it's
  not necessary to include those lower-level details for the moment.

*/

/********************************************************************
* Datatypes
********************************************************************/

abstract sig Thread {}
one sig A, B extends Thread {}
one sig Lock {
  -- NOTE: silent failure (unsat) if try to refer to flags'; that 
  --   should really produce a warning...
  var flags: set Thread
}


-- These sigs and fields only exist to make it easier to see 
-- which action is taken in a given state when viewing an instance.
-- They are not part of either the domain or the system, but are a 
-- convenience for debugging and understanding the model's output.
abstract sig Action {}
one sig EnterCS, ExitCS, RequestAccess, WithdrawRequest, 
        GrantAccess extends Action {}
one sig Readability {
  var nextAction: one Action
}

/********************************************************************
* Domain-controlled actions
********************************************************************/

-- Frame-condition helper: all _other_ threads' state is unchanged
pred othersSame[t: Thread] { 
	all t2: Thread - t |  t2 in Lock.flags' iff t2 in Lock.flags
}

-- These are not observable by the system
--    Analogy: "people waiting on floor X" from 4DC
pred enterCS[t: Thread] {
  Lock.flags' = Lock.flags -- FRAME: no change in system state
  Readability.nextAction = EnterCS -- VIEW
}
pred exitCS[t: Thread] {
  Lock.flags' = Lock.flags -- FRAME: no change in system state
  Readability.nextAction = ExitCS -- VIEW
}

-- These are observable by the system
--    Analogy: "someone presses the button on floor X" from 4DC
pred requestAccess[t: Thread] {
   t in Lock.flags' -- EFFECT
   othersSame[t]  -- FRAME
   Readability.nextAction = RequestAccess -- VIEW
}

-- Pred encodes what happens in the system when this action occurs
pred withdrawRequest[t: Thread] {
   t not in Lock.flags' -- EFFECT
   othersSame[t]  -- FRAME
   Readability.nextAction = WithdrawRequest -- FVIEW
}

/********************************************************************
* System-controlled actions
********************************************************************/

-- Can the system perform this action at this time?
pred grantAccessTo_Enabled[t: Thread] {
   t in Lock.flags
   all t2: Thread - t | t2 not in Lock.flags
}
-- What happens when the system performs this action?
pred grantAccessTo[t: Thread] {
   grantAccessTo_Enabled[t] -- GUARD
   Lock.flags' = Lock.flags -- FRAME

   Readability.nextAction = GrantAccess -- FOR READING

   -- NOTE: this action, as formulated, allows repeated grant actions.
}

/********************************************************************
* Transition system
********************************************************************/

pred initialState {
   all t: Thread | t not in Lock.flags
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

/********************************************************************
* Domain knowledge
*   In this model version, these cannot see the flags
*   These should not constrain the behavior or timing of grant
********************************************************************/

-- Once a thread requests, it won't request again until it finishes 
-- with the critical section. This also implies that threads won't 
-- withdraw their requests early.
pred dk_request_once {
  all t: Thread | {
    always { 
		requestAccess[t] implies 
			not requestAccess[t] until exitCS[t]
    }
  }
}
run consistent_dk_request_once {dk_request_once and someTrace} expect 1

-- A thread won't request access again if it has already been granted
-- for the most recent request
pred dk_no_request_if_already_granted {
  all t: Thread | 
    always {
      grantAccessTo[t] implies not requestAccess[t] until exitCS[t]
    }
}
run consistent_dk_no_request_if_already_granted 
  {dk_no_request_if_already_granted and someTrace} expect 1

-- Threads won't enter the critical section unless it has an active grant
-- Threads won't exit the critical section before entering
--   (Convenient to use past-time LTL)
pred dk_good_behavior {
  all t: Thread | 
    always {
      enterCS[t] implies not enterCS[t] since grantAccessTo[t]

      -- If exiting, entered some time in past without any intervening exit
      exitCS[t] implies not exitCS[t] since enterCS[t]
    }
}
run consistent_dk_good_behavior {dk_good_behavior and someTrace} expect 1

/********************************************************************
* Optional behavioral predicates
*    These can see the flags
*    These should not constrain the behavior or timing of any action 
*      but grant. However, they may reference domain-controlled actions 
*      (e.g., in the antecedents of implication)
********************************************************************/

-- We can express this by looking at flags (since this is behavioral)
pred behavior_shared_interest_flags {
  eventually {
    Lock.flags = Thread
  }
} 
-- ...or by events...
pred behavior_shared_interest_events {
  eventually {
    requestAccess[A] 
    not grantAccessTo[A] until requestAccess[B]
  } 
} 
run consistent_shared_interest_flags {
  someTrace and behavior_shared_interest_flags
} expect 1
run consistent_shared_interest_events {
  someTrace and behavior_shared_interest_events
} expect 1

-- Either way, that check isn't yet good enough; we need to 
--   cross-check consistency between DK and optional S here.

run consistent_shared_interest_with_dk_request_once {
  someTrace
  dk_request_once
  behavior_shared_interest_flags
} expect 1
-- ^ This fails (unsat).
-- Thus the transition system cannot produce a trace wherein
-- all threads are interested at once...

run consistent_shared_interest_with_dk_good_behavior {
  someTrace
  dk_good_behavior
  behavior_shared_interest_flags
} expect 1

/********************************************************************
* Requirements
********************************************************************/

-- Expect these to require domain knowledge connecting enter/exit and grant
--   Without that, these _pass_ (given that enter/exit can be taken whenever...)
assert require_mutualExclusion {
  { someTrace
    dk_good_behavior -- won't enter CS without approval, can't exit before enter
  } 

  implies

    all disj t, t2: Thread | { 
      always {
	    enterCS[t] => (not enterCS[t2] until exitCS[t])
      } } }
check require_mutualExclusion

assert require_nonStarvation {
  { someTrace
    dk_good_behavior -- won't enter CS without approval, can't exit before enter
    dk_request_once  -- don't request again until done with CS
  } 

  implies

    all t: Thread | {
      always { 
	    requestAccess[t] => eventually enterCS[t]
    } } }
check require_nonStarvation
