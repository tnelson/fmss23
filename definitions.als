abstract sig Card {value: one Int}
one sig Card1, Card2, Card3, Card4, Card5, Card6, Card7 extends Card {}

abstract sig Person {}
one sig A, B, C extends Person {}

abstract sig World {
	holds: Person one -> Card
}

abstract sig State {
    -- This defines the edges of a Kripke structure: w1->p->w2 is present
    -- if and only if person p, dwelling in world w1, believes it is possible
    -- that they actually inhabit world w2.
	possibleFrom: set World -> Person -> World
}
one sig Start, BSpoke, BothSpoke extends State {}

/********************************************************************
* Explicitly name all worlds to enable to below optimization.
* (This text was generated via a Python script.)
********************************************************************/

one sig World_1_234_567,World_1_235_467,World_1_236_457,World_1_237_456,World_1_245_367,World_1_246_357,World_1_247_356,World_1_256_347,World_1_257_346,World_1_267_345,World_1_345_267,World_1_346_257,World_1_347_256,World_1_356_247,World_1_357_246,World_1_367_245,World_1_456_237,World_1_457_236,World_1_467_235,World_1_567_234,World_2_134_567,World_2_135_467,World_2_136_457,World_2_137_456,World_2_145_367,World_2_146_357,World_2_147_356,World_2_156_347,World_2_157_346,World_2_167_345,World_2_345_167,World_2_346_157,World_2_347_156,World_2_356_147,World_2_357_146,World_2_367_145,World_2_456_137,World_2_457_136,World_2_467_135,World_2_567_134,World_3_124_567,World_3_125_467,World_3_126_457,World_3_127_456,World_3_145_267,World_3_146_257,World_3_147_256,World_3_156_247,World_3_157_246,World_3_167_245,World_3_245_167,World_3_246_157,World_3_247_156,World_3_256_147,World_3_257_146,World_3_267_145,World_3_456_127,World_3_457_126,World_3_467_125,World_3_567_124,World_4_123_567,World_4_125_367,World_4_126_357,World_4_127_356,World_4_135_267,World_4_136_257,World_4_137_256,World_4_156_237,World_4_157_236,World_4_167_235,World_4_235_167,World_4_236_157,World_4_237_156,World_4_256_137,World_4_257_136,World_4_267_135,World_4_356_127,World_4_357_126,World_4_367_125,World_4_567_123,World_5_123_467,World_5_124_367,World_5_126_347,World_5_127_346,World_5_134_267,World_5_136_247,World_5_137_246,World_5_146_237,World_5_147_236,World_5_167_234,World_5_234_167,World_5_236_147,World_5_237_146,World_5_246_137,World_5_247_136,World_5_267_134,World_5_346_127,World_5_347_126,World_5_367_124,World_5_467_123,World_6_123_457,World_6_124_357,World_6_125_347,World_6_127_345,World_6_134_257,World_6_135_247,World_6_137_245,World_6_145_237,World_6_147_235,World_6_157_234,World_6_234_157,World_6_235_147,World_6_237_145,World_6_245_137,World_6_247_135,World_6_257_134,World_6_345_127,World_6_347_125,World_6_357_124,World_6_457_123,World_7_123_456,World_7_124_356,World_7_125_346,World_7_126_345,World_7_134_256,World_7_135_246,World_7_136_245,World_7_145_236,World_7_146_235,World_7_156_234,World_7_234_156,World_7_235_146,World_7_236_145,World_7_245_136,World_7_246_135,World_7_256_134,World_7_345_126,World_7_346_125,World_7_356_124,World_7_456_123 extends World {}
