/**
	Model of knowledge puzzle from SSFM23

    Author's note: I initially wrote this expecting ststements about knowledge, 
    because the problem brought to mind the chained epistemic solutions seen in
    (e.g.) the muddy children puzzle. This is not actually required! However, 
    the framework can still be applied and so I am keeping it, even though it 
    is more heavyweight than strictly required to check the solution. It will
    also be a potential reference if one ever does need Kripke structures. :-)
  
    Tim Nelson (June 2023)


    *** PROBLEM STATEMENT ***

    There are 3 people: A, B, and C.
    There are 7 known cards, each containing one of the distinct natural 
    numbers 1 through 7. These are dealt to the 3 people, who know their 
    card(s) but not the card(s) of others. All people know _how many_ cards
    everyone receives. 
      - A draws 1 card; and
      - B and C each draw 3 cards.

    B says something openly to C (i.e., A can hear as well)
    C then says something openly to B.
    
    At this point, B and C both know exactly who has each card. But A does not
    know for certain who has *any* single card.

    What did B and C say to each other?
*/

open definitions
-- Holding the definition of the initial state in a separate
-- Alloy file, because my editor lags when it is open.
open partialInstance

/**
  Notes on executing this model:

  (1) Because there are 140 cards, the model is quite
  close to running against Alloy/Kodkod's native "no more than MAXINT possible
  tuples, before considering types" limitation. Running with 5 Int is, at the moment,
  OK (this adds 32 integer atoms, so 6+7 can be represented) but running with 7 Int is not. 

  (2) If you get a counterexample to a property, it may be hard to use the default 
  visualization. Instead, use tree-view and page down until you see a relation 
  starting with a dollar sign ($) and ending with w. This "w" relation denotes the 
  counterexample world. E.g., assuming that the cardValues and partialInstance facts
  are in effect, World_4_257_136 would denote that the assertion fails in a world 
  where A drew 4 and B drew 2, 5, and 7. 
  Then open the evaluator and use the `believesPossible` function to explore the 
  failure. E.g., if C does not gain enough knowledge, ask:
    believesPossible[BSpoke, World_4_257_136, C]
  to discover which worlds C believes are possible after B speaks.

  If the failing requirement is that A doesn't learn who holds any card, the 
  $ relations will involve "w" and "c" for the current world and card learned,
  respectively.
*/

-- Summing card values naively requires ability to count to (5+6+7) = 18
--   which is bitwidth = 6 ~~ interval [-32, 31]
-- However, if phrasing this so that summing the actual values is avoided, the 
--   viable bitwidth may be lower. E.g., if summing the _remainders_ modulo
--   (say) 7, then worst case is (4+5+6) = 15, which needs only bitwidth = 5 ~~ [-16, 15]
-- Further optimization is possible in this case by chaining single operations:
--   ((((4 mod 7) + (5 mod 7)) mod 7) + (6 mod 7)) mod 7
--   requires only counting to 5+6=11, which is /still/ bitwidth 5 ~~ [-16, 15] 
fact cardValues {
  -- This will not be picked up by Alloy's partial-instance inference
//  Card1.value = 1
// ...

  -- This will be:
  value = Card1->1 + Card2->2 + Card3->3 + Card4->4 + 
          Card5->5 + Card6->6 + Card7->7
}

/********************************************************************
* Starting knowledge state and how knowledge changes over time
*   and various helper functions
********************************************************************/

pred baseKnowledge {
	-- Every person knows what cards they hold, and nothing else
    Start.possibleFrom = {w: World, p: Person, w2: World | 
		w.holds[p] = w2.holds[p]
    }
}

fun numberAdjacent[w: World, p: Person]: Int {
	#(w.holds[p] -> w.holds[p] & (
		Card1 -> Card2 + Card2 -> Card3 + Card3 -> Card4 + 
        Card4 -> Card5 + Card5 -> Card6 + Card6 -> Card7 
    ))
}

fun totalParity[w: World, p: Person]: Int {
  rem[#((Card1 + Card3 + Card5 + Card7) & w.holds[p]), 2]
}

-- NOTE WELL the comment above the value field declaration.
-- This operation is carefully crafted to not require counting above M.
-- ...there is almost certainly a more efficient way to do this.
//fun sumModulo[w: World, p: Person, M: Int]: Int {
//  let small  = {c : w.holds[p]                  | all other : w.holds[p] - c                  | other.value > c.value} |
//  let middle = {c : w.holds[p] - small          | all other : w.holds[p] - c - small          | other.value > c.value} |
//  let large  = {c : w.holds[p] - small - middle | all other : w.holds[p] - c - small - middle | other.value > c.value} |
//    rem[add[rem[add[small.value, middle.value], 
//                M], 
//            large.value], 
//        M]
//}
fun smallestCard[cards: set Card]: lone Card {
	Card1 in cards => Card1 else
    Card2 in cards => Card2 else
	Card3 in cards => Card3 else
	Card4 in cards => Card4 else
	Card5 in cards => Card5 else
	Card6 in cards => Card6 else
	Card7
}
fun sumModulo[w: World, p: Person, M: Int]: Int {
  let small  = smallestCard[w.holds[p]] | 
  let middle = smallestCard[w.holds[p] - small] | 
  let large  = smallestCard[w.holds[p] - middle - small] | 
  let result = 
            rem[add[rem[add[small.value, middle.value], 
                M], 
            large.value], 
        M] |
  -- Alloy can produce negative remainders in case of overflow 
  -- (which should not happen, but just in case, replace very strange results with
  --  mildly strange ones)
  result < 0 => add[result, 7] else result
}


fun believesPossible[s: State, inWorld: World, p: Person]: set World {
    s.possibleFrom[inWorld][p]
}

-- The change in knowledge after B speaks
pred BSpeaks {
	BSpoke.possibleFrom = Start.possibleFrom & 

    -- "The number of cards c in my hand that immediately succeed some other card in my hand is..."
    --{w: World, p: Person, w2: World | numberAdjacent[w, B] = numberAdjacent[w2, B]}

	-- "The total parity of my cards is..."
	--{w: World, p: Person, w2: World | totalParity[w, B] = totalParity[w2, B]}

    -- "The sum of my cards modulo 7 is..."
	{w: World, p: Person, w2: World | sumModulo[w, B, 7] = sumModulo[w2, B, 7]}

    -- "The sum of the cards I (B) do not have modulo 7 is..."
//    {w: World, p: Person, w2: World | 
//      rem[add[sumModulo[w,  A, 7], sumModulo[w,  C, 7]], 7] =
//      rem[add[sumModulo[w2, A, 7], sumModulo[w2, C, 7]], 7] }

}

-- The change in knowledge after C speaks
pred CSpeaks {
	BothSpoke.possibleFrom = BSpoke.possibleFrom & 

    -- "The sum of my cards modulo 7 is..."
	{w: World, p: Person, w2: World | sumModulo[w, C, 7] = sumModulo[w2, C, 7]}


    -- "The sum of the cards I (C) do not have modulo 7 is..."
//    {w: World, p: Person, w2: World | 
//      rem[add[sumModulo[w,  A, 7], sumModulo[w,  B, 7]], 7] =
//      rem[add[sumModulo[w2, A, 7], sumModulo[w2, B, 7]], 7] }
}

//run {baseKnowledge and BSpeaks and CSpeaks} 
//  for exactly 3 State, exactly 7 Card, exactly 140 World, 5 Int
//  expect 1

/********************************************************************
* Requirements (the goals of the puzzle)
*   - B and C eventually get certsain knowledge for all cards
*   - A does not ever get certain knowledge for any card
********************************************************************/


assert knowledge_is_consistent_with_reality {
    {baseKnowledge and BSpeaks and CSpeaks} implies

	all s: State, p: Person, w: World | {
		w in s.possibleFrom[w][p]
	}
}
check knowledge_is_consistent_with_reality 
  for exactly 3 State, exactly 7 Card, exactly 140 World, 5 Int

-- Requirement: C has learned who has all numbers after both speak
assert req_C_knows_numbers {
    {baseKnowledge and BSpeaks and CSpeaks} implies
	all w: World | {
		BothSpoke.possibleFrom[w][C] = w
    }
}
check req_C_knows_numbers 
  for exactly 3 State, exactly 7 Card, exactly 140 World, 5 Int

-- Requirement: B has learned who has all numbers after both speak
assert req_B_knows_numbers {
    {baseKnowledge and BSpeaks and CSpeaks} implies
	all w: World | {
		BothSpoke.possibleFrom[w][B] = w
    }
}
check req_B_knows_numbers 
  for exactly 3 State, exactly 7 Card, exactly 140 World, 5 Int

-- Requirement: even after both speak, A does not know for certain who
-- holds each card. That is, while A's knowledge may grow, it remains the
-- case that whichever world w is true, there are always two distinct worlds 
-- that A considers possible based on the information spoken in w.

pred c_learns_nothing_in[w: World] {
    -- for every card except the one that A holds in this world
	all c: Card - w.holds[A] | {
        -- there is uncertainty for this card if the real situation is world w
		some disj possw1, possw2: BothSpoke.possibleFrom[w][A] | {
            c in possw1.holds[B] and c in possw2.holds[C]
        }
    }
}
assert req_A_knows_no_numbers {
    {baseKnowledge and BSpeaks and CSpeaks} implies
	all w: World | c_learns_nothing_in[w]
}
check req_A_knows_no_numbers 
  for exactly 3 State, exactly 7 Card, exactly 140 World, 5 Int


/********************************************************************
* Validation
********************************************************************/

-- General satisfiability of the full scenario
-- TODO: isn't there only one instance here? (why isn't partial-instance inference working?)
//run scenario_sat {baseKnowledge and BSpeaks and CSpeaks} 
//  for exactly 3 State, exactly 7 Card, exactly 140 World, 5 Int
//  expect 1

-- Satisfiability of A learning a cardholder if we don't constrain what C says
run a_learns_if_c_unconstrained {
    baseKnowledge and BSpeaks and some w: World | not c_learns_nothing_in[w]} 
  for exactly 3 State, exactly 7 Card, exactly 140 World, 5 Int
  expect 1

