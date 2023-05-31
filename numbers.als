/**
	Model of knowledge puzzle from SSFM23
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

abstract sig Card {value: one Int}
one sig Card1, Card2, Card3, Card4, Card5, Card6, Card7 extends Card {}

/**
  Notes on executing this model:

  (1) Because there are 140 cards, the model is quite
  close to running against Alloy/Kodkod's native "no more than MAXINT possible
  tuples, before considering types" limitation. Running with 4 Int is, at the moment,
  OK, but running with 7 Int is not.

  (2) If you get a counterexample to a property, it may be hard to use the default 
  visualization. Instead, use tree-view and page down until you see a relation 
  starting with a dollar sign ($). This denotes the counterexample world. E.g., 
  World_4_257_136 would denote that the assertion fails in a world where A drew 4
  and B drew 2, 5, and 7. Then open the evaluator and use the `believesPossible` 
  function to explore the failure. E.g., if C does not gain enough knowledge, ask:
    believesPossible[BSpoke, World_4_257_136, C]
  to discover which worlds C believes are possible after B speaks.
*/

-- NOTE WELL: if summing card values, requires ability to count to (5+6+7) = 18
--   which is bitwidth = 6 ~~ interval [-32, 31]
-- However, if phrasing this so that summing the actual values is avoided, the 
--   viable bitwidth may be lower. E.g., if summing the _remainders_ modulo
--   (say) 7, then worst case is (4+5+6) = 15, which needs only bitwidth = 5 ~~ [-16, 15]
-- Further optimization is possible in this case by chaining single operations:
--   ((((4 mod 7) + (5 mod 7)) mod 7) + (6 mod 7)) mod 7
--   requires only counting to 7, which is bitwidth 4 ~~ [-8, 7] 
fact cardValues {
  Card1.value = 1
  Card2.value = 2
  Card3.value = 3
  Card4.value = 4
  Card5.value = 5
  Card6.value = 6
  Card7.value = 7
}

abstract sig Person {}
one sig A, B, C extends Person {}

abstract sig World {
	holds: Person one -> Card
}

abstract sig State {
	possibleFrom: set World -> Person -> World
}
one sig Start, BSpoke, BothSpoke extends State {}

/********************************************************************
* Explicitly name all worlds, to enable to below optimization.
* (This was generated via a Python script.)
********************************************************************/

one sig World_1_234_567,World_1_235_467,World_1_236_457,World_1_237_456,World_1_245_367,World_1_246_357,World_1_247_356,World_1_256_347,World_1_257_346,World_1_267_345,World_1_345_267,World_1_346_257,World_1_347_256,World_1_356_247,World_1_357_246,World_1_367_245,World_1_456_237,World_1_457_236,World_1_467_235,World_1_567_234,World_2_134_567,World_2_135_467,World_2_136_457,World_2_137_456,World_2_145_367,World_2_146_357,World_2_147_356,World_2_156_347,World_2_157_346,World_2_167_345,World_2_345_167,World_2_346_157,World_2_347_156,World_2_356_147,World_2_357_146,World_2_367_145,World_2_456_137,World_2_457_136,World_2_467_135,World_2_567_134,World_3_124_567,World_3_125_467,World_3_126_457,World_3_127_456,World_3_145_267,World_3_146_257,World_3_147_256,World_3_156_247,World_3_157_246,World_3_167_245,World_3_245_167,World_3_246_157,World_3_247_156,World_3_256_147,World_3_257_146,World_3_267_145,World_3_456_127,World_3_457_126,World_3_467_125,World_3_567_124,World_4_123_567,World_4_125_367,World_4_126_357,World_4_127_356,World_4_135_267,World_4_136_257,World_4_137_256,World_4_156_237,World_4_157_236,World_4_167_235,World_4_235_167,World_4_236_157,World_4_237_156,World_4_256_137,World_4_257_136,World_4_267_135,World_4_356_127,World_4_357_126,World_4_367_125,World_4_567_123,World_5_123_467,World_5_124_367,World_5_126_347,World_5_127_346,World_5_134_267,World_5_136_247,World_5_137_246,World_5_146_237,World_5_147_236,World_5_167_234,World_5_234_167,World_5_236_147,World_5_237_146,World_5_246_137,World_5_247_136,World_5_267_134,World_5_346_127,World_5_347_126,World_5_367_124,World_5_467_123,World_6_123_457,World_6_124_357,World_6_125_347,World_6_127_345,World_6_134_257,World_6_135_247,World_6_137_245,World_6_145_237,World_6_147_235,World_6_157_234,World_6_234_157,World_6_235_147,World_6_237_145,World_6_245_137,World_6_247_135,World_6_257_134,World_6_345_127,World_6_347_125,World_6_357_124,World_6_457_123,World_7_123_456,World_7_124_356,World_7_125_346,World_7_126_345,World_7_134_256,World_7_135_246,World_7_136_245,World_7_145_236,World_7_146_235,World_7_156_234,World_7_234_156,World_7_235_146,World_7_236_145,World_7_245_136,World_7_246_135,World_7_256_134,World_7_345_126,World_7_346_125,World_7_356_124,World_7_456_123 extends World {}

/********************************************************************
* Optimization: rather than leaving Alloy to solve for card-holding 
* configurations in each world based on constraints, explicitly define
* them all in a partial instance. 
* (This was generated via a Python script.)
********************************************************************/


fact partialInstance {
World_1_234_567.holds = A->Card1 + B->Card2+B->Card3+B->Card4 + C->Card5+C->Card6+C->Card7
World_1_235_467.holds = A->Card1 + B->Card2+B->Card3+B->Card5 + C->Card4+C->Card6+C->Card7
World_1_236_457.holds = A->Card1 + B->Card2+B->Card3+B->Card6 + C->Card4+C->Card5+C->Card7
World_1_237_456.holds = A->Card1 + B->Card2+B->Card3+B->Card7 + C->Card4+C->Card5+C->Card6
World_1_245_367.holds = A->Card1 + B->Card2+B->Card4+B->Card5 + C->Card3+C->Card6+C->Card7
World_1_246_357.holds = A->Card1 + B->Card2+B->Card4+B->Card6 + C->Card3+C->Card5+C->Card7
World_1_247_356.holds = A->Card1 + B->Card2+B->Card4+B->Card7 + C->Card3+C->Card5+C->Card6
World_1_256_347.holds = A->Card1 + B->Card2+B->Card5+B->Card6 + C->Card3+C->Card4+C->Card7
World_1_257_346.holds = A->Card1 + B->Card2+B->Card5+B->Card7 + C->Card3+C->Card4+C->Card6
World_1_267_345.holds = A->Card1 + B->Card2+B->Card6+B->Card7 + C->Card3+C->Card4+C->Card5
World_1_345_267.holds = A->Card1 + B->Card3+B->Card4+B->Card5 + C->Card2+C->Card6+C->Card7
World_1_346_257.holds = A->Card1 + B->Card3+B->Card4+B->Card6 + C->Card2+C->Card5+C->Card7
World_1_347_256.holds = A->Card1 + B->Card3+B->Card4+B->Card7 + C->Card2+C->Card5+C->Card6
World_1_356_247.holds = A->Card1 + B->Card3+B->Card5+B->Card6 + C->Card2+C->Card4+C->Card7
World_1_357_246.holds = A->Card1 + B->Card3+B->Card5+B->Card7 + C->Card2+C->Card4+C->Card6
World_1_367_245.holds = A->Card1 + B->Card3+B->Card6+B->Card7 + C->Card2+C->Card4+C->Card5
World_1_456_237.holds = A->Card1 + B->Card4+B->Card5+B->Card6 + C->Card2+C->Card3+C->Card7
World_1_457_236.holds = A->Card1 + B->Card4+B->Card5+B->Card7 + C->Card2+C->Card3+C->Card6
World_1_467_235.holds = A->Card1 + B->Card4+B->Card6+B->Card7 + C->Card2+C->Card3+C->Card5
World_1_567_234.holds = A->Card1 + B->Card5+B->Card6+B->Card7 + C->Card2+C->Card3+C->Card4
World_2_134_567.holds = A->Card2 + B->Card1+B->Card3+B->Card4 + C->Card5+C->Card6+C->Card7
World_2_135_467.holds = A->Card2 + B->Card1+B->Card3+B->Card5 + C->Card4+C->Card6+C->Card7
World_2_136_457.holds = A->Card2 + B->Card1+B->Card3+B->Card6 + C->Card4+C->Card5+C->Card7
World_2_137_456.holds = A->Card2 + B->Card1+B->Card3+B->Card7 + C->Card4+C->Card5+C->Card6
World_2_145_367.holds = A->Card2 + B->Card1+B->Card4+B->Card5 + C->Card3+C->Card6+C->Card7
World_2_146_357.holds = A->Card2 + B->Card1+B->Card4+B->Card6 + C->Card3+C->Card5+C->Card7
World_2_147_356.holds = A->Card2 + B->Card1+B->Card4+B->Card7 + C->Card3+C->Card5+C->Card6
World_2_156_347.holds = A->Card2 + B->Card1+B->Card5+B->Card6 + C->Card3+C->Card4+C->Card7
World_2_157_346.holds = A->Card2 + B->Card1+B->Card5+B->Card7 + C->Card3+C->Card4+C->Card6
World_2_167_345.holds = A->Card2 + B->Card1+B->Card6+B->Card7 + C->Card3+C->Card4+C->Card5
World_2_345_167.holds = A->Card2 + B->Card3+B->Card4+B->Card5 + C->Card1+C->Card6+C->Card7
World_2_346_157.holds = A->Card2 + B->Card3+B->Card4+B->Card6 + C->Card1+C->Card5+C->Card7
World_2_347_156.holds = A->Card2 + B->Card3+B->Card4+B->Card7 + C->Card1+C->Card5+C->Card6
World_2_356_147.holds = A->Card2 + B->Card3+B->Card5+B->Card6 + C->Card1+C->Card4+C->Card7
World_2_357_146.holds = A->Card2 + B->Card3+B->Card5+B->Card7 + C->Card1+C->Card4+C->Card6
World_2_367_145.holds = A->Card2 + B->Card3+B->Card6+B->Card7 + C->Card1+C->Card4+C->Card5
World_2_456_137.holds = A->Card2 + B->Card4+B->Card5+B->Card6 + C->Card1+C->Card3+C->Card7
World_2_457_136.holds = A->Card2 + B->Card4+B->Card5+B->Card7 + C->Card1+C->Card3+C->Card6
World_2_467_135.holds = A->Card2 + B->Card4+B->Card6+B->Card7 + C->Card1+C->Card3+C->Card5
World_2_567_134.holds = A->Card2 + B->Card5+B->Card6+B->Card7 + C->Card1+C->Card3+C->Card4
World_3_124_567.holds = A->Card3 + B->Card1+B->Card2+B->Card4 + C->Card5+C->Card6+C->Card7
World_3_125_467.holds = A->Card3 + B->Card1+B->Card2+B->Card5 + C->Card4+C->Card6+C->Card7
World_3_126_457.holds = A->Card3 + B->Card1+B->Card2+B->Card6 + C->Card4+C->Card5+C->Card7
World_3_127_456.holds = A->Card3 + B->Card1+B->Card2+B->Card7 + C->Card4+C->Card5+C->Card6
World_3_145_267.holds = A->Card3 + B->Card1+B->Card4+B->Card5 + C->Card2+C->Card6+C->Card7
World_3_146_257.holds = A->Card3 + B->Card1+B->Card4+B->Card6 + C->Card2+C->Card5+C->Card7
World_3_147_256.holds = A->Card3 + B->Card1+B->Card4+B->Card7 + C->Card2+C->Card5+C->Card6
World_3_156_247.holds = A->Card3 + B->Card1+B->Card5+B->Card6 + C->Card2+C->Card4+C->Card7
World_3_157_246.holds = A->Card3 + B->Card1+B->Card5+B->Card7 + C->Card2+C->Card4+C->Card6
World_3_167_245.holds = A->Card3 + B->Card1+B->Card6+B->Card7 + C->Card2+C->Card4+C->Card5
World_3_245_167.holds = A->Card3 + B->Card2+B->Card4+B->Card5 + C->Card1+C->Card6+C->Card7
World_3_246_157.holds = A->Card3 + B->Card2+B->Card4+B->Card6 + C->Card1+C->Card5+C->Card7
World_3_247_156.holds = A->Card3 + B->Card2+B->Card4+B->Card7 + C->Card1+C->Card5+C->Card6
World_3_256_147.holds = A->Card3 + B->Card2+B->Card5+B->Card6 + C->Card1+C->Card4+C->Card7
World_3_257_146.holds = A->Card3 + B->Card2+B->Card5+B->Card7 + C->Card1+C->Card4+C->Card6
World_3_267_145.holds = A->Card3 + B->Card2+B->Card6+B->Card7 + C->Card1+C->Card4+C->Card5
World_3_456_127.holds = A->Card3 + B->Card4+B->Card5+B->Card6 + C->Card1+C->Card2+C->Card7
World_3_457_126.holds = A->Card3 + B->Card4+B->Card5+B->Card7 + C->Card1+C->Card2+C->Card6
World_3_467_125.holds = A->Card3 + B->Card4+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card5
World_3_567_124.holds = A->Card3 + B->Card5+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card4
World_4_123_567.holds = A->Card4 + B->Card1+B->Card2+B->Card3 + C->Card5+C->Card6+C->Card7
World_4_125_367.holds = A->Card4 + B->Card1+B->Card2+B->Card5 + C->Card3+C->Card6+C->Card7
World_4_126_357.holds = A->Card4 + B->Card1+B->Card2+B->Card6 + C->Card3+C->Card5+C->Card7
World_4_127_356.holds = A->Card4 + B->Card1+B->Card2+B->Card7 + C->Card3+C->Card5+C->Card6
World_4_135_267.holds = A->Card4 + B->Card1+B->Card3+B->Card5 + C->Card2+C->Card6+C->Card7
World_4_136_257.holds = A->Card4 + B->Card1+B->Card3+B->Card6 + C->Card2+C->Card5+C->Card7
World_4_137_256.holds = A->Card4 + B->Card1+B->Card3+B->Card7 + C->Card2+C->Card5+C->Card6
World_4_156_237.holds = A->Card4 + B->Card1+B->Card5+B->Card6 + C->Card2+C->Card3+C->Card7
World_4_157_236.holds = A->Card4 + B->Card1+B->Card5+B->Card7 + C->Card2+C->Card3+C->Card6
World_4_167_235.holds = A->Card4 + B->Card1+B->Card6+B->Card7 + C->Card2+C->Card3+C->Card5
World_4_235_167.holds = A->Card4 + B->Card2+B->Card3+B->Card5 + C->Card1+C->Card6+C->Card7
World_4_236_157.holds = A->Card4 + B->Card2+B->Card3+B->Card6 + C->Card1+C->Card5+C->Card7
World_4_237_156.holds = A->Card4 + B->Card2+B->Card3+B->Card7 + C->Card1+C->Card5+C->Card6
World_4_256_137.holds = A->Card4 + B->Card2+B->Card5+B->Card6 + C->Card1+C->Card3+C->Card7
World_4_257_136.holds = A->Card4 + B->Card2+B->Card5+B->Card7 + C->Card1+C->Card3+C->Card6
World_4_267_135.holds = A->Card4 + B->Card2+B->Card6+B->Card7 + C->Card1+C->Card3+C->Card5
World_4_356_127.holds = A->Card4 + B->Card3+B->Card5+B->Card6 + C->Card1+C->Card2+C->Card7
World_4_357_126.holds = A->Card4 + B->Card3+B->Card5+B->Card7 + C->Card1+C->Card2+C->Card6
World_4_367_125.holds = A->Card4 + B->Card3+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card5
World_4_567_123.holds = A->Card4 + B->Card5+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card3
World_5_123_467.holds = A->Card5 + B->Card1+B->Card2+B->Card3 + C->Card4+C->Card6+C->Card7
World_5_124_367.holds = A->Card5 + B->Card1+B->Card2+B->Card4 + C->Card3+C->Card6+C->Card7
World_5_126_347.holds = A->Card5 + B->Card1+B->Card2+B->Card6 + C->Card3+C->Card4+C->Card7
World_5_127_346.holds = A->Card5 + B->Card1+B->Card2+B->Card7 + C->Card3+C->Card4+C->Card6
World_5_134_267.holds = A->Card5 + B->Card1+B->Card3+B->Card4 + C->Card2+C->Card6+C->Card7
World_5_136_247.holds = A->Card5 + B->Card1+B->Card3+B->Card6 + C->Card2+C->Card4+C->Card7
World_5_137_246.holds = A->Card5 + B->Card1+B->Card3+B->Card7 + C->Card2+C->Card4+C->Card6
World_5_146_237.holds = A->Card5 + B->Card1+B->Card4+B->Card6 + C->Card2+C->Card3+C->Card7
World_5_147_236.holds = A->Card5 + B->Card1+B->Card4+B->Card7 + C->Card2+C->Card3+C->Card6
World_5_167_234.holds = A->Card5 + B->Card1+B->Card6+B->Card7 + C->Card2+C->Card3+C->Card4
World_5_234_167.holds = A->Card5 + B->Card2+B->Card3+B->Card4 + C->Card1+C->Card6+C->Card7
World_5_236_147.holds = A->Card5 + B->Card2+B->Card3+B->Card6 + C->Card1+C->Card4+C->Card7
World_5_237_146.holds = A->Card5 + B->Card2+B->Card3+B->Card7 + C->Card1+C->Card4+C->Card6
World_5_246_137.holds = A->Card5 + B->Card2+B->Card4+B->Card6 + C->Card1+C->Card3+C->Card7
World_5_247_136.holds = A->Card5 + B->Card2+B->Card4+B->Card7 + C->Card1+C->Card3+C->Card6
World_5_267_134.holds = A->Card5 + B->Card2+B->Card6+B->Card7 + C->Card1+C->Card3+C->Card4
World_5_346_127.holds = A->Card5 + B->Card3+B->Card4+B->Card6 + C->Card1+C->Card2+C->Card7
World_5_347_126.holds = A->Card5 + B->Card3+B->Card4+B->Card7 + C->Card1+C->Card2+C->Card6
World_5_367_124.holds = A->Card5 + B->Card3+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card4
World_5_467_123.holds = A->Card5 + B->Card4+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card3
World_6_123_457.holds = A->Card6 + B->Card1+B->Card2+B->Card3 + C->Card4+C->Card5+C->Card7
World_6_124_357.holds = A->Card6 + B->Card1+B->Card2+B->Card4 + C->Card3+C->Card5+C->Card7
World_6_125_347.holds = A->Card6 + B->Card1+B->Card2+B->Card5 + C->Card3+C->Card4+C->Card7
World_6_127_345.holds = A->Card6 + B->Card1+B->Card2+B->Card7 + C->Card3+C->Card4+C->Card5
World_6_134_257.holds = A->Card6 + B->Card1+B->Card3+B->Card4 + C->Card2+C->Card5+C->Card7
World_6_135_247.holds = A->Card6 + B->Card1+B->Card3+B->Card5 + C->Card2+C->Card4+C->Card7
World_6_137_245.holds = A->Card6 + B->Card1+B->Card3+B->Card7 + C->Card2+C->Card4+C->Card5
World_6_145_237.holds = A->Card6 + B->Card1+B->Card4+B->Card5 + C->Card2+C->Card3+C->Card7
World_6_147_235.holds = A->Card6 + B->Card1+B->Card4+B->Card7 + C->Card2+C->Card3+C->Card5
World_6_157_234.holds = A->Card6 + B->Card1+B->Card5+B->Card7 + C->Card2+C->Card3+C->Card4
World_6_234_157.holds = A->Card6 + B->Card2+B->Card3+B->Card4 + C->Card1+C->Card5+C->Card7
World_6_235_147.holds = A->Card6 + B->Card2+B->Card3+B->Card5 + C->Card1+C->Card4+C->Card7
World_6_237_145.holds = A->Card6 + B->Card2+B->Card3+B->Card7 + C->Card1+C->Card4+C->Card5
World_6_245_137.holds = A->Card6 + B->Card2+B->Card4+B->Card5 + C->Card1+C->Card3+C->Card7
World_6_247_135.holds = A->Card6 + B->Card2+B->Card4+B->Card7 + C->Card1+C->Card3+C->Card5
World_6_257_134.holds = A->Card6 + B->Card2+B->Card5+B->Card7 + C->Card1+C->Card3+C->Card4
World_6_345_127.holds = A->Card6 + B->Card3+B->Card4+B->Card5 + C->Card1+C->Card2+C->Card7
World_6_347_125.holds = A->Card6 + B->Card3+B->Card4+B->Card7 + C->Card1+C->Card2+C->Card5
World_6_357_124.holds = A->Card6 + B->Card3+B->Card5+B->Card7 + C->Card1+C->Card2+C->Card4
World_6_457_123.holds = A->Card6 + B->Card4+B->Card5+B->Card7 + C->Card1+C->Card2+C->Card3
World_7_123_456.holds = A->Card7 + B->Card1+B->Card2+B->Card3 + C->Card4+C->Card5+C->Card6
World_7_124_356.holds = A->Card7 + B->Card1+B->Card2+B->Card4 + C->Card3+C->Card5+C->Card6
World_7_125_346.holds = A->Card7 + B->Card1+B->Card2+B->Card5 + C->Card3+C->Card4+C->Card6
World_7_126_345.holds = A->Card7 + B->Card1+B->Card2+B->Card6 + C->Card3+C->Card4+C->Card5
World_7_134_256.holds = A->Card7 + B->Card1+B->Card3+B->Card4 + C->Card2+C->Card5+C->Card6
World_7_135_246.holds = A->Card7 + B->Card1+B->Card3+B->Card5 + C->Card2+C->Card4+C->Card6
World_7_136_245.holds = A->Card7 + B->Card1+B->Card3+B->Card6 + C->Card2+C->Card4+C->Card5
World_7_145_236.holds = A->Card7 + B->Card1+B->Card4+B->Card5 + C->Card2+C->Card3+C->Card6
World_7_146_235.holds = A->Card7 + B->Card1+B->Card4+B->Card6 + C->Card2+C->Card3+C->Card5
World_7_156_234.holds = A->Card7 + B->Card1+B->Card5+B->Card6 + C->Card2+C->Card3+C->Card4
World_7_234_156.holds = A->Card7 + B->Card2+B->Card3+B->Card4 + C->Card1+C->Card5+C->Card6
World_7_235_146.holds = A->Card7 + B->Card2+B->Card3+B->Card5 + C->Card1+C->Card4+C->Card6
World_7_236_145.holds = A->Card7 + B->Card2+B->Card3+B->Card6 + C->Card1+C->Card4+C->Card5
World_7_245_136.holds = A->Card7 + B->Card2+B->Card4+B->Card5 + C->Card1+C->Card3+C->Card6
World_7_246_135.holds = A->Card7 + B->Card2+B->Card4+B->Card6 + C->Card1+C->Card3+C->Card5
World_7_256_134.holds = A->Card7 + B->Card2+B->Card5+B->Card6 + C->Card1+C->Card3+C->Card4
World_7_345_126.holds = A->Card7 + B->Card3+B->Card4+B->Card5 + C->Card1+C->Card2+C->Card6
World_7_346_125.holds = A->Card7 + B->Card3+B->Card4+B->Card6 + C->Card1+C->Card2+C->Card5
World_7_356_124.holds = A->Card7 + B->Card3+B->Card5+B->Card6 + C->Card1+C->Card2+C->Card4
World_7_456_123.holds = A->Card7 + B->Card4+B->Card5+B->Card6 + C->Card1+C->Card2+C->Card3
}


-- This could be replaced with a partial instance
//pred dealCards {
//    all w: World | {
//		#w.holds[A] = 1
//        #w.holds[B] = 3
//        #w.holds[C] = 3
//    }
//	all disj w1, w2: World | {
//		w1.holds != w2.holds
//    }
//}

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
    rem[add[rem[add[small.value, middle.value], 
                M], 
            large.value], 
        M]
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

}

-- The change in knowledge after C speaks
pred CSpeaks {
    -- say nothing (YET) in 2nd round
	BSpoke.possibleFrom = BothSpoke.possibleFrom
}

run {baseKnowledge and BSpeaks and CSpeaks} 
  for exactly 3 State, exactly 7 Card, exactly 140 World, 4 Int
  expect 1

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
  for exactly 3 State, exactly 7 Card, exactly 140 World, 4 Int

-- Requirement: C has learned who has all numbers after both speak
assert req_C_knows_numbers {
    {baseKnowledge and BSpeaks and CSpeaks} implies
	all w: World | {
		BothSpoke.possibleFrom[w][C] = w
    }
}
check req_C_knows_numbers 
  for exactly 3 State, exactly 7 Card, exactly 140 World, 4 Int

-- Requirement: B has learned who has all numbers after both speak
assert req_B_knows_numbers {
    {baseKnowledge and BSpeaks and CSpeaks} implies
	all w: World | {
		BothSpoke.possibleFrom[w][B] = w
    }
}
check req_B_knows_numbers 
  for exactly 3 State, exactly 7 Card, exactly 140 World, 4 Int

-- Requirement: even after both speak, A does not know for certain who
-- holds each card. That is, while A's knowledge may grow, it remains the
-- case that whichever world w is true, there are always two distinct worlds 
-- that A considers possible based on the information spoken in w.
assert req_A_knows_no_numbers {
    {baseKnowledge and BSpeaks and CSpeaks} implies
	all w: World, c: Card | {
        -- there is uncertainty for this card if the real situation is world w
		some disj possw1, possw2: BothSpoke.possibleFrom[w][A] | {
            c in possw1.holds[B] and c in possw2.holds[C]
        }
    }
}
check req_A_knows_no_numbers 
  for exactly 3 State, exactly 7 Card, exactly 140 World, 4 Int

