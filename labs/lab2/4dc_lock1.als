/**
  Yet another Lock 1, more faithful to "four dark corners"
  (Key: step back, don't model *slides* too closely)


  Informal:  ... TODO

  Semiformal: ... TODO




  Domain: Programs contending

  Controls:
	- enter[pid] 
      ? not in old model
	- exit[pid] 
      ? not in old model
	- request[pid] (iface)
      ? Feels like old model only allowed "successful requests"?
      but the guard _constrains the domain_ -- should be a DK predicate, not in spec
	- withdraw[pid] (iface)
      ? Feels like old model only allowed "successful requests"? -- ditto as above

  Spec: Lock system
  
  Controls:
	- grant[pid] (iface)

*/

abstract sig Thread {}
one sig A, B extends Thread {}
one sig Lock {
  -- NOTE: silent failure (unsat) if try to refer to
  --  flags' (suggest adding a warning here?)
  var flags: set Thread
}

-- To make it easier to see which action is taken
-- This isn't part of the spec/domain
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
  Lock.flags' = Lock.flags -- FRAME
  Readability.nextAction = EnterCS -- FOR READING
}
pred exitCS[t: Thread] {
  Lock.flags' = Lock.flags -- FRAME
  Readability.nextAction = ExitCS -- FOR READING
}

-- These are observable by the system
--    Analogy: "someone presses the button on floor X" from 4DC
-- Pred encodes what happens in the system when this action occurs
pred requestAccess[t: Thread] {
   t in Lock.flags' -- EFFECT
   othersSame[t]  -- FRAME
   Readability.nextAction = RequestAccess -- FOR READING
}

-- Pred encodes what happens in the system when this action occurs
pred withdrawRequest[t: Thread] {
   t not in Lock.flags' -- EFFECT
   othersSame[t]  -- FRAME
   Readability.nextAction = WithdrawRequest -- FOR READING
}

/********************************************************************
* System-controlled actions
********************************************************************/

-- Can the system perform the action at this time?
pred grantAccessTo_Enabled[t: Thread] {
   t in Lock.flags
   all t2: Thread - t | t2 not in Lock.flags
}
-- What happens when the system performs this action?
pred grantAccessTo[t: Thread] {
   grantAccessTo_Enabled[t] -- GUARD
   Lock.flags' = Lock.flags -- FRAME

   Readability.nextAction = GrantAccess -- FOR READING

-- TODO: this allows repeated grants
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

-- A thread won't request if it's in the critical section or has yet to process a grant
-- ...

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


-- 

/********************************************************************
* Optional behavioral predicates
*    These can see the flags
*    These should not constrain the behavior or timing of any action 
*      but grant but may reference domain-controlled actions (e.g., 
*      in antecedents)
********************************************************************/

-- We can express this by looking at flags (since this is behavioral)/
pred behavior_shared_interest_flags {
  eventually {
    Lock.flags = Thread
  }
} 
-- ...or by events
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
-- ^ Thus the transition system cannot produce a trace wherein
-- all threads are interested...

-- Note dk_request_once is used in the non-starvation requirement!

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
