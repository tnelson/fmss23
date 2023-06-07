
/********************************************************************
* Optimization: rather than leaving Alloy to solve for card-holding 
* configurations in each world based on constraints, explicitly define
* them all in a partial instance. 
*   Note well: make sure "infer partial instance" is turned on in Options.
* (This text was generated via a Python script.)
********************************************************************/

open definitions

-- May not yet be enough to infer (depends on RHS)
-- Also seems like there's no _lower_ bound inferred? 
--   but just upper should be a big help.
-- With verbosity debug on, this causes a NullPointerException

//fact partialInstanceConcise {
//holds = 
//(World_1_234_567 -> (A->Card1 + B->Card2+B->Card3+B->Card4 + C->Card5+C->Card6+C->Card7))+
//(World_1_235_467 -> (A->Card1 + B->Card2+B->Card3+B->Card5 + C->Card4+C->Card6+C->Card7))+
//(World_1_236_457 -> (A->Card1 + B->Card2+B->Card3+B->Card6 + C->Card4+C->Card5+C->Card7))+
//(World_1_237_456 -> (A->Card1 + B->Card2+B->Card3+B->Card7 + C->Card4+C->Card5+C->Card6))+
//(World_1_245_367 -> (A->Card1 + B->Card2+B->Card4+B->Card5 + C->Card3+C->Card6+C->Card7))+
//(World_1_246_357 -> (A->Card1 + B->Card2+B->Card4+B->Card6 + C->Card3+C->Card5+C->Card7))+
//(World_1_247_356 -> (A->Card1 + B->Card2+B->Card4+B->Card7 + C->Card3+C->Card5+C->Card6))+
//(World_1_256_347 -> (A->Card1 + B->Card2+B->Card5+B->Card6 + C->Card3+C->Card4+C->Card7))+
//(World_1_257_346 -> (A->Card1 + B->Card2+B->Card5+B->Card7 + C->Card3+C->Card4+C->Card6))+
//(World_1_267_345 -> (A->Card1 + B->Card2+B->Card6+B->Card7 + C->Card3+C->Card4+C->Card5))+
//(World_1_345_267 -> (A->Card1 + B->Card3+B->Card4+B->Card5 + C->Card2+C->Card6+C->Card7))+
//(World_1_346_257 -> (A->Card1 + B->Card3+B->Card4+B->Card6 + C->Card2+C->Card5+C->Card7))+
//(World_1_347_256 -> (A->Card1 + B->Card3+B->Card4+B->Card7 + C->Card2+C->Card5+C->Card6))+
//(World_1_356_247 -> (A->Card1 + B->Card3+B->Card5+B->Card6 + C->Card2+C->Card4+C->Card7))+
//(World_1_357_246 -> (A->Card1 + B->Card3+B->Card5+B->Card7 + C->Card2+C->Card4+C->Card6))+
//(World_1_367_245 -> (A->Card1 + B->Card3+B->Card6+B->Card7 + C->Card2+C->Card4+C->Card5))+
//(World_1_456_237 -> (A->Card1 + B->Card4+B->Card5+B->Card6 + C->Card2+C->Card3+C->Card7))+
//(World_1_457_236 -> (A->Card1 + B->Card4+B->Card5+B->Card7 + C->Card2+C->Card3+C->Card6))+
//(World_1_467_235 -> (A->Card1 + B->Card4+B->Card6+B->Card7 + C->Card2+C->Card3+C->Card5))+
//(World_1_567_234 -> (A->Card1 + B->Card5+B->Card6+B->Card7 + C->Card2+C->Card3+C->Card4))+
//(World_2_134_567 -> (A->Card2 + B->Card1+B->Card3+B->Card4 + C->Card5+C->Card6+C->Card7))+
//(World_2_135_467 -> (A->Card2 + B->Card1+B->Card3+B->Card5 + C->Card4+C->Card6+C->Card7))+
//(World_2_136_457 -> (A->Card2 + B->Card1+B->Card3+B->Card6 + C->Card4+C->Card5+C->Card7))+
//(World_2_137_456 -> (A->Card2 + B->Card1+B->Card3+B->Card7 + C->Card4+C->Card5+C->Card6))+
//(World_2_145_367 -> (A->Card2 + B->Card1+B->Card4+B->Card5 + C->Card3+C->Card6+C->Card7))+
//(World_2_146_357 -> (A->Card2 + B->Card1+B->Card4+B->Card6 + C->Card3+C->Card5+C->Card7))+
//(World_2_147_356 -> (A->Card2 + B->Card1+B->Card4+B->Card7 + C->Card3+C->Card5+C->Card6))+
//(World_2_156_347 -> (A->Card2 + B->Card1+B->Card5+B->Card6 + C->Card3+C->Card4+C->Card7))+
//(World_2_157_346 -> (A->Card2 + B->Card1+B->Card5+B->Card7 + C->Card3+C->Card4+C->Card6))+
//(World_2_167_345 -> (A->Card2 + B->Card1+B->Card6+B->Card7 + C->Card3+C->Card4+C->Card5))+
//(World_2_345_167 -> (A->Card2 + B->Card3+B->Card4+B->Card5 + C->Card1+C->Card6+C->Card7))+
//(World_2_346_157 -> (A->Card2 + B->Card3+B->Card4+B->Card6 + C->Card1+C->Card5+C->Card7))+
//(World_2_347_156 -> (A->Card2 + B->Card3+B->Card4+B->Card7 + C->Card1+C->Card5+C->Card6))+
//(World_2_356_147 -> (A->Card2 + B->Card3+B->Card5+B->Card6 + C->Card1+C->Card4+C->Card7))+
//(World_2_357_146 -> (A->Card2 + B->Card3+B->Card5+B->Card7 + C->Card1+C->Card4+C->Card6))+
//(World_2_367_145 -> (A->Card2 + B->Card3+B->Card6+B->Card7 + C->Card1+C->Card4+C->Card5))+
//(World_2_456_137 -> (A->Card2 + B->Card4+B->Card5+B->Card6 + C->Card1+C->Card3+C->Card7))+
//(World_2_457_136 -> (A->Card2 + B->Card4+B->Card5+B->Card7 + C->Card1+C->Card3+C->Card6))+
//(World_2_467_135 -> (A->Card2 + B->Card4+B->Card6+B->Card7 + C->Card1+C->Card3+C->Card5))+
//(World_2_567_134 -> (A->Card2 + B->Card5+B->Card6+B->Card7 + C->Card1+C->Card3+C->Card4))+
//(World_3_124_567 -> (A->Card3 + B->Card1+B->Card2+B->Card4 + C->Card5+C->Card6+C->Card7))+
//(World_3_125_467 -> (A->Card3 + B->Card1+B->Card2+B->Card5 + C->Card4+C->Card6+C->Card7))+
//(World_3_126_457 -> (A->Card3 + B->Card1+B->Card2+B->Card6 + C->Card4+C->Card5+C->Card7))+
//(World_3_127_456 -> (A->Card3 + B->Card1+B->Card2+B->Card7 + C->Card4+C->Card5+C->Card6))+
//(World_3_145_267 -> (A->Card3 + B->Card1+B->Card4+B->Card5 + C->Card2+C->Card6+C->Card7))+
//(World_3_146_257 -> (A->Card3 + B->Card1+B->Card4+B->Card6 + C->Card2+C->Card5+C->Card7))+
//(World_3_147_256 -> (A->Card3 + B->Card1+B->Card4+B->Card7 + C->Card2+C->Card5+C->Card6))+
//(World_3_156_247 -> (A->Card3 + B->Card1+B->Card5+B->Card6 + C->Card2+C->Card4+C->Card7))+
//(World_3_157_246 -> (A->Card3 + B->Card1+B->Card5+B->Card7 + C->Card2+C->Card4+C->Card6))+
//(World_3_167_245 -> (A->Card3 + B->Card1+B->Card6+B->Card7 + C->Card2+C->Card4+C->Card5))+
//(World_3_245_167 -> (A->Card3 + B->Card2+B->Card4+B->Card5 + C->Card1+C->Card6+C->Card7))+
//(World_3_246_157 -> (A->Card3 + B->Card2+B->Card4+B->Card6 + C->Card1+C->Card5+C->Card7))+
//(World_3_247_156 -> (A->Card3 + B->Card2+B->Card4+B->Card7 + C->Card1+C->Card5+C->Card6))+
//(World_3_256_147 -> (A->Card3 + B->Card2+B->Card5+B->Card6 + C->Card1+C->Card4+C->Card7))+
//(World_3_257_146 -> (A->Card3 + B->Card2+B->Card5+B->Card7 + C->Card1+C->Card4+C->Card6))+
//(World_3_267_145 -> (A->Card3 + B->Card2+B->Card6+B->Card7 + C->Card1+C->Card4+C->Card5))+
//(World_3_456_127 -> (A->Card3 + B->Card4+B->Card5+B->Card6 + C->Card1+C->Card2+C->Card7))+
//(World_3_457_126 -> (A->Card3 + B->Card4+B->Card5+B->Card7 + C->Card1+C->Card2+C->Card6))+
//(World_3_467_125 -> (A->Card3 + B->Card4+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card5))+
//(World_3_567_124 -> (A->Card3 + B->Card5+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card4))+
//(World_4_123_567 -> (A->Card4 + B->Card1+B->Card2+B->Card3 + C->Card5+C->Card6+C->Card7))+
//(World_4_125_367 -> (A->Card4 + B->Card1+B->Card2+B->Card5 + C->Card3+C->Card6+C->Card7))+
//(World_4_126_357 -> (A->Card4 + B->Card1+B->Card2+B->Card6 + C->Card3+C->Card5+C->Card7))+
//(World_4_127_356 -> (A->Card4 + B->Card1+B->Card2+B->Card7 + C->Card3+C->Card5+C->Card6))+
//(World_4_135_267 -> (A->Card4 + B->Card1+B->Card3+B->Card5 + C->Card2+C->Card6+C->Card7))+
//(World_4_136_257 -> (A->Card4 + B->Card1+B->Card3+B->Card6 + C->Card2+C->Card5+C->Card7))+
//(World_4_137_256 -> (A->Card4 + B->Card1+B->Card3+B->Card7 + C->Card2+C->Card5+C->Card6))+
//(World_4_156_237 -> (A->Card4 + B->Card1+B->Card5+B->Card6 + C->Card2+C->Card3+C->Card7))+
//(World_4_157_236 -> (A->Card4 + B->Card1+B->Card5+B->Card7 + C->Card2+C->Card3+C->Card6))+
//(World_4_167_235 -> (A->Card4 + B->Card1+B->Card6+B->Card7 + C->Card2+C->Card3+C->Card5))+
//(World_4_235_167 -> (A->Card4 + B->Card2+B->Card3+B->Card5 + C->Card1+C->Card6+C->Card7))+
//(World_4_236_157 -> (A->Card4 + B->Card2+B->Card3+B->Card6 + C->Card1+C->Card5+C->Card7))+
//(World_4_237_156 -> (A->Card4 + B->Card2+B->Card3+B->Card7 + C->Card1+C->Card5+C->Card6))+
//(World_4_256_137 -> (A->Card4 + B->Card2+B->Card5+B->Card6 + C->Card1+C->Card3+C->Card7))+
//(World_4_257_136 -> (A->Card4 + B->Card2+B->Card5+B->Card7 + C->Card1+C->Card3+C->Card6))+
//(World_4_267_135 -> (A->Card4 + B->Card2+B->Card6+B->Card7 + C->Card1+C->Card3+C->Card5))+
//(World_4_356_127 -> (A->Card4 + B->Card3+B->Card5+B->Card6 + C->Card1+C->Card2+C->Card7))+
//(World_4_357_126 -> (A->Card4 + B->Card3+B->Card5+B->Card7 + C->Card1+C->Card2+C->Card6))+
//(World_4_367_125 -> (A->Card4 + B->Card3+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card5))+
//(World_4_567_123 -> (A->Card4 + B->Card5+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card3))+
//(World_5_123_467 -> (A->Card5 + B->Card1+B->Card2+B->Card3 + C->Card4+C->Card6+C->Card7))+
//(World_5_124_367 -> (A->Card5 + B->Card1+B->Card2+B->Card4 + C->Card3+C->Card6+C->Card7))+
//(World_5_126_347 -> (A->Card5 + B->Card1+B->Card2+B->Card6 + C->Card3+C->Card4+C->Card7))+
//(World_5_127_346 -> (A->Card5 + B->Card1+B->Card2+B->Card7 + C->Card3+C->Card4+C->Card6))+
//(World_5_134_267 -> (A->Card5 + B->Card1+B->Card3+B->Card4 + C->Card2+C->Card6+C->Card7))+
//(World_5_136_247 -> (A->Card5 + B->Card1+B->Card3+B->Card6 + C->Card2+C->Card4+C->Card7))+
//(World_5_137_246 -> (A->Card5 + B->Card1+B->Card3+B->Card7 + C->Card2+C->Card4+C->Card6))+
//(World_5_146_237 -> (A->Card5 + B->Card1+B->Card4+B->Card6 + C->Card2+C->Card3+C->Card7))+
//(World_5_147_236 -> (A->Card5 + B->Card1+B->Card4+B->Card7 + C->Card2+C->Card3+C->Card6))+
//(World_5_167_234 -> (A->Card5 + B->Card1+B->Card6+B->Card7 + C->Card2+C->Card3+C->Card4))+
//(World_5_234_167 -> (A->Card5 + B->Card2+B->Card3+B->Card4 + C->Card1+C->Card6+C->Card7))+
//(World_5_236_147 -> (A->Card5 + B->Card2+B->Card3+B->Card6 + C->Card1+C->Card4+C->Card7))+
//(World_5_237_146 -> (A->Card5 + B->Card2+B->Card3+B->Card7 + C->Card1+C->Card4+C->Card6))+
//(World_5_246_137 -> (A->Card5 + B->Card2+B->Card4+B->Card6 + C->Card1+C->Card3+C->Card7))+
//(World_5_247_136 -> (A->Card5 + B->Card2+B->Card4+B->Card7 + C->Card1+C->Card3+C->Card6))+
//(World_5_267_134 -> (A->Card5 + B->Card2+B->Card6+B->Card7 + C->Card1+C->Card3+C->Card4))+
//(World_5_346_127 -> (A->Card5 + B->Card3+B->Card4+B->Card6 + C->Card1+C->Card2+C->Card7))+
//(World_5_347_126 -> (A->Card5 + B->Card3+B->Card4+B->Card7 + C->Card1+C->Card2+C->Card6))+
//(World_5_367_124 -> (A->Card5 + B->Card3+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card4))+
//(World_5_467_123 -> (A->Card5 + B->Card4+B->Card6+B->Card7 + C->Card1+C->Card2+C->Card3))+
//(World_6_123_457 -> (A->Card6 + B->Card1+B->Card2+B->Card3 + C->Card4+C->Card5+C->Card7))+
//(World_6_124_357 -> (A->Card6 + B->Card1+B->Card2+B->Card4 + C->Card3+C->Card5+C->Card7))+
//(World_6_125_347 -> (A->Card6 + B->Card1+B->Card2+B->Card5 + C->Card3+C->Card4+C->Card7))+
//(World_6_127_345 -> (A->Card6 + B->Card1+B->Card2+B->Card7 + C->Card3+C->Card4+C->Card5))+
//(World_6_134_257 -> (A->Card6 + B->Card1+B->Card3+B->Card4 + C->Card2+C->Card5+C->Card7))+
//(World_6_135_247 -> (A->Card6 + B->Card1+B->Card3+B->Card5 + C->Card2+C->Card4+C->Card7))+
//(World_6_137_245 -> (A->Card6 + B->Card1+B->Card3+B->Card7 + C->Card2+C->Card4+C->Card5))+
//(World_6_145_237 -> (A->Card6 + B->Card1+B->Card4+B->Card5 + C->Card2+C->Card3+C->Card7))+
//(World_6_147_235 -> (A->Card6 + B->Card1+B->Card4+B->Card7 + C->Card2+C->Card3+C->Card5))+
//(World_6_157_234 -> (A->Card6 + B->Card1+B->Card5+B->Card7 + C->Card2+C->Card3+C->Card4))+
//(World_6_234_157 -> (A->Card6 + B->Card2+B->Card3+B->Card4 + C->Card1+C->Card5+C->Card7))+
//(World_6_235_147 -> (A->Card6 + B->Card2+B->Card3+B->Card5 + C->Card1+C->Card4+C->Card7))+
//(World_6_237_145 -> (A->Card6 + B->Card2+B->Card3+B->Card7 + C->Card1+C->Card4+C->Card5))+
//(World_6_245_137 -> (A->Card6 + B->Card2+B->Card4+B->Card5 + C->Card1+C->Card3+C->Card7))+
//(World_6_247_135 -> (A->Card6 + B->Card2+B->Card4+B->Card7 + C->Card1+C->Card3+C->Card5))+
//(World_6_257_134 -> (A->Card6 + B->Card2+B->Card5+B->Card7 + C->Card1+C->Card3+C->Card4))+
//(World_6_345_127 -> (A->Card6 + B->Card3+B->Card4+B->Card5 + C->Card1+C->Card2+C->Card7))+
//(World_6_347_125 -> (A->Card6 + B->Card3+B->Card4+B->Card7 + C->Card1+C->Card2+C->Card5))+
//(World_6_357_124 -> (A->Card6 + B->Card3+B->Card5+B->Card7 + C->Card1+C->Card2+C->Card4))+
//(World_6_457_123 -> (A->Card6 + B->Card4+B->Card5+B->Card7 + C->Card1+C->Card2+C->Card3))+
//(World_7_123_456 -> (A->Card7 + B->Card1+B->Card2+B->Card3 + C->Card4+C->Card5+C->Card6))+
//(World_7_124_356 -> (A->Card7 + B->Card1+B->Card2+B->Card4 + C->Card3+C->Card5+C->Card6))+
//(World_7_125_346 -> (A->Card7 + B->Card1+B->Card2+B->Card5 + C->Card3+C->Card4+C->Card6))+
//(World_7_126_345 -> (A->Card7 + B->Card1+B->Card2+B->Card6 + C->Card3+C->Card4+C->Card5))+
//(World_7_134_256 -> (A->Card7 + B->Card1+B->Card3+B->Card4 + C->Card2+C->Card5+C->Card6))+
//(World_7_135_246 -> (A->Card7 + B->Card1+B->Card3+B->Card5 + C->Card2+C->Card4+C->Card6))+
//(World_7_136_245 -> (A->Card7 + B->Card1+B->Card3+B->Card6 + C->Card2+C->Card4+C->Card5))+
//(World_7_145_236 -> (A->Card7 + B->Card1+B->Card4+B->Card5 + C->Card2+C->Card3+C->Card6))+
//(World_7_146_235 -> (A->Card7 + B->Card1+B->Card4+B->Card6 + C->Card2+C->Card3+C->Card5))+
//(World_7_156_234 -> (A->Card7 + B->Card1+B->Card5+B->Card6 + C->Card2+C->Card3+C->Card4))+
//(World_7_234_156 -> (A->Card7 + B->Card2+B->Card3+B->Card4 + C->Card1+C->Card5+C->Card6))+
//(World_7_235_146 -> (A->Card7 + B->Card2+B->Card3+B->Card5 + C->Card1+C->Card4+C->Card6))+
//(World_7_236_145 -> (A->Card7 + B->Card2+B->Card3+B->Card6 + C->Card1+C->Card4+C->Card5))+
//(World_7_245_136 -> (A->Card7 + B->Card2+B->Card4+B->Card5 + C->Card1+C->Card3+C->Card6))+
//(World_7_246_135 -> (A->Card7 + B->Card2+B->Card4+B->Card6 + C->Card1+C->Card3+C->Card5))+
//(World_7_256_134 -> (A->Card7 + B->Card2+B->Card5+B->Card6 + C->Card1+C->Card3+C->Card4))+
//(World_7_345_126 -> (A->Card7 + B->Card3+B->Card4+B->Card5 + C->Card1+C->Card2+C->Card6))+
//(World_7_346_125 -> (A->Card7 + B->Card3+B->Card4+B->Card6 + C->Card1+C->Card2+C->Card5))+
//(World_7_356_124 -> (A->Card7 + B->Card3+B->Card5+B->Card6 + C->Card1+C->Card2+C->Card4))+
//(World_7_456_123 -> (A->Card7 + B->Card4+B->Card5+B->Card6 + C->Card1+C->Card2+C->Card3))
//
//}

fact partialInstance {
holds = 
World_1_234_567->A->Card1 + World_1_234_567->B->Card2+World_1_234_567->B->Card3+World_1_234_567->B->Card4 + World_1_234_567->C->Card5+World_1_234_567->C->Card6+World_1_234_567->C->Card7+
World_1_235_467->A->Card1 + World_1_235_467->B->Card2+World_1_235_467->B->Card3+World_1_235_467->B->Card5 + World_1_235_467->C->Card4+World_1_235_467->C->Card6+World_1_235_467->C->Card7+
World_1_236_457->A->Card1 + World_1_236_457->B->Card2+World_1_236_457->B->Card3+World_1_236_457->B->Card6 + World_1_236_457->C->Card4+World_1_236_457->C->Card5+World_1_236_457->C->Card7+
World_1_237_456->A->Card1 + World_1_237_456->B->Card2+World_1_237_456->B->Card3+World_1_237_456->B->Card7 + World_1_237_456->C->Card4+World_1_237_456->C->Card5+World_1_237_456->C->Card6+
World_1_245_367->A->Card1 + World_1_245_367->B->Card2+World_1_245_367->B->Card4+World_1_245_367->B->Card5 + World_1_245_367->C->Card3+World_1_245_367->C->Card6+World_1_245_367->C->Card7+
World_1_246_357->A->Card1 + World_1_246_357->B->Card2+World_1_246_357->B->Card4+World_1_246_357->B->Card6 + World_1_246_357->C->Card3+World_1_246_357->C->Card5+World_1_246_357->C->Card7+
World_1_247_356->A->Card1 + World_1_247_356->B->Card2+World_1_247_356->B->Card4+World_1_247_356->B->Card7 + World_1_247_356->C->Card3+World_1_247_356->C->Card5+World_1_247_356->C->Card6+
World_1_256_347->A->Card1 + World_1_256_347->B->Card2+World_1_256_347->B->Card5+World_1_256_347->B->Card6 + World_1_256_347->C->Card3+World_1_256_347->C->Card4+World_1_256_347->C->Card7+
World_1_257_346->A->Card1 + World_1_257_346->B->Card2+World_1_257_346->B->Card5+World_1_257_346->B->Card7 + World_1_257_346->C->Card3+World_1_257_346->C->Card4+World_1_257_346->C->Card6+
World_1_267_345->A->Card1 + World_1_267_345->B->Card2+World_1_267_345->B->Card6+World_1_267_345->B->Card7 + World_1_267_345->C->Card3+World_1_267_345->C->Card4+World_1_267_345->C->Card5+
World_1_345_267->A->Card1 + World_1_345_267->B->Card3+World_1_345_267->B->Card4+World_1_345_267->B->Card5 + World_1_345_267->C->Card2+World_1_345_267->C->Card6+World_1_345_267->C->Card7+
World_1_346_257->A->Card1 + World_1_346_257->B->Card3+World_1_346_257->B->Card4+World_1_346_257->B->Card6 + World_1_346_257->C->Card2+World_1_346_257->C->Card5+World_1_346_257->C->Card7+
World_1_347_256->A->Card1 + World_1_347_256->B->Card3+World_1_347_256->B->Card4+World_1_347_256->B->Card7 + World_1_347_256->C->Card2+World_1_347_256->C->Card5+World_1_347_256->C->Card6+
World_1_356_247->A->Card1 + World_1_356_247->B->Card3+World_1_356_247->B->Card5+World_1_356_247->B->Card6 + World_1_356_247->C->Card2+World_1_356_247->C->Card4+World_1_356_247->C->Card7+
World_1_357_246->A->Card1 + World_1_357_246->B->Card3+World_1_357_246->B->Card5+World_1_357_246->B->Card7 + World_1_357_246->C->Card2+World_1_357_246->C->Card4+World_1_357_246->C->Card6+
World_1_367_245->A->Card1 + World_1_367_245->B->Card3+World_1_367_245->B->Card6+World_1_367_245->B->Card7 + World_1_367_245->C->Card2+World_1_367_245->C->Card4+World_1_367_245->C->Card5+
World_1_456_237->A->Card1 + World_1_456_237->B->Card4+World_1_456_237->B->Card5+World_1_456_237->B->Card6 + World_1_456_237->C->Card2+World_1_456_237->C->Card3+World_1_456_237->C->Card7+
World_1_457_236->A->Card1 + World_1_457_236->B->Card4+World_1_457_236->B->Card5+World_1_457_236->B->Card7 + World_1_457_236->C->Card2+World_1_457_236->C->Card3+World_1_457_236->C->Card6+
World_1_467_235->A->Card1 + World_1_467_235->B->Card4+World_1_467_235->B->Card6+World_1_467_235->B->Card7 + World_1_467_235->C->Card2+World_1_467_235->C->Card3+World_1_467_235->C->Card5+
World_1_567_234->A->Card1 + World_1_567_234->B->Card5+World_1_567_234->B->Card6+World_1_567_234->B->Card7 + World_1_567_234->C->Card2+World_1_567_234->C->Card3+World_1_567_234->C->Card4+
World_2_134_567->A->Card2 + World_2_134_567->B->Card1+World_2_134_567->B->Card3+World_2_134_567->B->Card4 + World_2_134_567->C->Card5+World_2_134_567->C->Card6+World_2_134_567->C->Card7+
World_2_135_467->A->Card2 + World_2_135_467->B->Card1+World_2_135_467->B->Card3+World_2_135_467->B->Card5 + World_2_135_467->C->Card4+World_2_135_467->C->Card6+World_2_135_467->C->Card7+
World_2_136_457->A->Card2 + World_2_136_457->B->Card1+World_2_136_457->B->Card3+World_2_136_457->B->Card6 + World_2_136_457->C->Card4+World_2_136_457->C->Card5+World_2_136_457->C->Card7+
World_2_137_456->A->Card2 + World_2_137_456->B->Card1+World_2_137_456->B->Card3+World_2_137_456->B->Card7 + World_2_137_456->C->Card4+World_2_137_456->C->Card5+World_2_137_456->C->Card6+
World_2_145_367->A->Card2 + World_2_145_367->B->Card1+World_2_145_367->B->Card4+World_2_145_367->B->Card5 + World_2_145_367->C->Card3+World_2_145_367->C->Card6+World_2_145_367->C->Card7+
World_2_146_357->A->Card2 + World_2_146_357->B->Card1+World_2_146_357->B->Card4+World_2_146_357->B->Card6 + World_2_146_357->C->Card3+World_2_146_357->C->Card5+World_2_146_357->C->Card7+
World_2_147_356->A->Card2 + World_2_147_356->B->Card1+World_2_147_356->B->Card4+World_2_147_356->B->Card7 + World_2_147_356->C->Card3+World_2_147_356->C->Card5+World_2_147_356->C->Card6+
World_2_156_347->A->Card2 + World_2_156_347->B->Card1+World_2_156_347->B->Card5+World_2_156_347->B->Card6 + World_2_156_347->C->Card3+World_2_156_347->C->Card4+World_2_156_347->C->Card7+
World_2_157_346->A->Card2 + World_2_157_346->B->Card1+World_2_157_346->B->Card5+World_2_157_346->B->Card7 + World_2_157_346->C->Card3+World_2_157_346->C->Card4+World_2_157_346->C->Card6+
World_2_167_345->A->Card2 + World_2_167_345->B->Card1+World_2_167_345->B->Card6+World_2_167_345->B->Card7 + World_2_167_345->C->Card3+World_2_167_345->C->Card4+World_2_167_345->C->Card5+
World_2_345_167->A->Card2 + World_2_345_167->B->Card3+World_2_345_167->B->Card4+World_2_345_167->B->Card5 + World_2_345_167->C->Card1+World_2_345_167->C->Card6+World_2_345_167->C->Card7+
World_2_346_157->A->Card2 + World_2_346_157->B->Card3+World_2_346_157->B->Card4+World_2_346_157->B->Card6 + World_2_346_157->C->Card1+World_2_346_157->C->Card5+World_2_346_157->C->Card7+
World_2_347_156->A->Card2 + World_2_347_156->B->Card3+World_2_347_156->B->Card4+World_2_347_156->B->Card7 + World_2_347_156->C->Card1+World_2_347_156->C->Card5+World_2_347_156->C->Card6+
World_2_356_147->A->Card2 + World_2_356_147->B->Card3+World_2_356_147->B->Card5+World_2_356_147->B->Card6 + World_2_356_147->C->Card1+World_2_356_147->C->Card4+World_2_356_147->C->Card7+
World_2_357_146->A->Card2 + World_2_357_146->B->Card3+World_2_357_146->B->Card5+World_2_357_146->B->Card7 + World_2_357_146->C->Card1+World_2_357_146->C->Card4+World_2_357_146->C->Card6+
World_2_367_145->A->Card2 + World_2_367_145->B->Card3+World_2_367_145->B->Card6+World_2_367_145->B->Card7 + World_2_367_145->C->Card1+World_2_367_145->C->Card4+World_2_367_145->C->Card5+
World_2_456_137->A->Card2 + World_2_456_137->B->Card4+World_2_456_137->B->Card5+World_2_456_137->B->Card6 + World_2_456_137->C->Card1+World_2_456_137->C->Card3+World_2_456_137->C->Card7+
World_2_457_136->A->Card2 + World_2_457_136->B->Card4+World_2_457_136->B->Card5+World_2_457_136->B->Card7 + World_2_457_136->C->Card1+World_2_457_136->C->Card3+World_2_457_136->C->Card6+
World_2_467_135->A->Card2 + World_2_467_135->B->Card4+World_2_467_135->B->Card6+World_2_467_135->B->Card7 + World_2_467_135->C->Card1+World_2_467_135->C->Card3+World_2_467_135->C->Card5+
World_2_567_134->A->Card2 + World_2_567_134->B->Card5+World_2_567_134->B->Card6+World_2_567_134->B->Card7 + World_2_567_134->C->Card1+World_2_567_134->C->Card3+World_2_567_134->C->Card4+
World_3_124_567->A->Card3 + World_3_124_567->B->Card1+World_3_124_567->B->Card2+World_3_124_567->B->Card4 + World_3_124_567->C->Card5+World_3_124_567->C->Card6+World_3_124_567->C->Card7+
World_3_125_467->A->Card3 + World_3_125_467->B->Card1+World_3_125_467->B->Card2+World_3_125_467->B->Card5 + World_3_125_467->C->Card4+World_3_125_467->C->Card6+World_3_125_467->C->Card7+
World_3_126_457->A->Card3 + World_3_126_457->B->Card1+World_3_126_457->B->Card2+World_3_126_457->B->Card6 + World_3_126_457->C->Card4+World_3_126_457->C->Card5+World_3_126_457->C->Card7+
World_3_127_456->A->Card3 + World_3_127_456->B->Card1+World_3_127_456->B->Card2+World_3_127_456->B->Card7 + World_3_127_456->C->Card4+World_3_127_456->C->Card5+World_3_127_456->C->Card6+
World_3_145_267->A->Card3 + World_3_145_267->B->Card1+World_3_145_267->B->Card4+World_3_145_267->B->Card5 + World_3_145_267->C->Card2+World_3_145_267->C->Card6+World_3_145_267->C->Card7+
World_3_146_257->A->Card3 + World_3_146_257->B->Card1+World_3_146_257->B->Card4+World_3_146_257->B->Card6 + World_3_146_257->C->Card2+World_3_146_257->C->Card5+World_3_146_257->C->Card7+
World_3_147_256->A->Card3 + World_3_147_256->B->Card1+World_3_147_256->B->Card4+World_3_147_256->B->Card7 + World_3_147_256->C->Card2+World_3_147_256->C->Card5+World_3_147_256->C->Card6+
World_3_156_247->A->Card3 + World_3_156_247->B->Card1+World_3_156_247->B->Card5+World_3_156_247->B->Card6 + World_3_156_247->C->Card2+World_3_156_247->C->Card4+World_3_156_247->C->Card7+
World_3_157_246->A->Card3 + World_3_157_246->B->Card1+World_3_157_246->B->Card5+World_3_157_246->B->Card7 + World_3_157_246->C->Card2+World_3_157_246->C->Card4+World_3_157_246->C->Card6+
World_3_167_245->A->Card3 + World_3_167_245->B->Card1+World_3_167_245->B->Card6+World_3_167_245->B->Card7 + World_3_167_245->C->Card2+World_3_167_245->C->Card4+World_3_167_245->C->Card5+
World_3_245_167->A->Card3 + World_3_245_167->B->Card2+World_3_245_167->B->Card4+World_3_245_167->B->Card5 + World_3_245_167->C->Card1+World_3_245_167->C->Card6+World_3_245_167->C->Card7+
World_3_246_157->A->Card3 + World_3_246_157->B->Card2+World_3_246_157->B->Card4+World_3_246_157->B->Card6 + World_3_246_157->C->Card1+World_3_246_157->C->Card5+World_3_246_157->C->Card7+
World_3_247_156->A->Card3 + World_3_247_156->B->Card2+World_3_247_156->B->Card4+World_3_247_156->B->Card7 + World_3_247_156->C->Card1+World_3_247_156->C->Card5+World_3_247_156->C->Card6+
World_3_256_147->A->Card3 + World_3_256_147->B->Card2+World_3_256_147->B->Card5+World_3_256_147->B->Card6 + World_3_256_147->C->Card1+World_3_256_147->C->Card4+World_3_256_147->C->Card7+
World_3_257_146->A->Card3 + World_3_257_146->B->Card2+World_3_257_146->B->Card5+World_3_257_146->B->Card7 + World_3_257_146->C->Card1+World_3_257_146->C->Card4+World_3_257_146->C->Card6+
World_3_267_145->A->Card3 + World_3_267_145->B->Card2+World_3_267_145->B->Card6+World_3_267_145->B->Card7 + World_3_267_145->C->Card1+World_3_267_145->C->Card4+World_3_267_145->C->Card5+
World_3_456_127->A->Card3 + World_3_456_127->B->Card4+World_3_456_127->B->Card5+World_3_456_127->B->Card6 + World_3_456_127->C->Card1+World_3_456_127->C->Card2+World_3_456_127->C->Card7+
World_3_457_126->A->Card3 + World_3_457_126->B->Card4+World_3_457_126->B->Card5+World_3_457_126->B->Card7 + World_3_457_126->C->Card1+World_3_457_126->C->Card2+World_3_457_126->C->Card6+
World_3_467_125->A->Card3 + World_3_467_125->B->Card4+World_3_467_125->B->Card6+World_3_467_125->B->Card7 + World_3_467_125->C->Card1+World_3_467_125->C->Card2+World_3_467_125->C->Card5+
World_3_567_124->A->Card3 + World_3_567_124->B->Card5+World_3_567_124->B->Card6+World_3_567_124->B->Card7 + World_3_567_124->C->Card1+World_3_567_124->C->Card2+World_3_567_124->C->Card4+
World_4_123_567->A->Card4 + World_4_123_567->B->Card1+World_4_123_567->B->Card2+World_4_123_567->B->Card3 + World_4_123_567->C->Card5+World_4_123_567->C->Card6+World_4_123_567->C->Card7+
World_4_125_367->A->Card4 + World_4_125_367->B->Card1+World_4_125_367->B->Card2+World_4_125_367->B->Card5 + World_4_125_367->C->Card3+World_4_125_367->C->Card6+World_4_125_367->C->Card7+
World_4_126_357->A->Card4 + World_4_126_357->B->Card1+World_4_126_357->B->Card2+World_4_126_357->B->Card6 + World_4_126_357->C->Card3+World_4_126_357->C->Card5+World_4_126_357->C->Card7+
World_4_127_356->A->Card4 + World_4_127_356->B->Card1+World_4_127_356->B->Card2+World_4_127_356->B->Card7 + World_4_127_356->C->Card3+World_4_127_356->C->Card5+World_4_127_356->C->Card6+
World_4_135_267->A->Card4 + World_4_135_267->B->Card1+World_4_135_267->B->Card3+World_4_135_267->B->Card5 + World_4_135_267->C->Card2+World_4_135_267->C->Card6+World_4_135_267->C->Card7+
World_4_136_257->A->Card4 + World_4_136_257->B->Card1+World_4_136_257->B->Card3+World_4_136_257->B->Card6 + World_4_136_257->C->Card2+World_4_136_257->C->Card5+World_4_136_257->C->Card7+
World_4_137_256->A->Card4 + World_4_137_256->B->Card1+World_4_137_256->B->Card3+World_4_137_256->B->Card7 + World_4_137_256->C->Card2+World_4_137_256->C->Card5+World_4_137_256->C->Card6+
World_4_156_237->A->Card4 + World_4_156_237->B->Card1+World_4_156_237->B->Card5+World_4_156_237->B->Card6 + World_4_156_237->C->Card2+World_4_156_237->C->Card3+World_4_156_237->C->Card7+
World_4_157_236->A->Card4 + World_4_157_236->B->Card1+World_4_157_236->B->Card5+World_4_157_236->B->Card7 + World_4_157_236->C->Card2+World_4_157_236->C->Card3+World_4_157_236->C->Card6+
World_4_167_235->A->Card4 + World_4_167_235->B->Card1+World_4_167_235->B->Card6+World_4_167_235->B->Card7 + World_4_167_235->C->Card2+World_4_167_235->C->Card3+World_4_167_235->C->Card5+
World_4_235_167->A->Card4 + World_4_235_167->B->Card2+World_4_235_167->B->Card3+World_4_235_167->B->Card5 + World_4_235_167->C->Card1+World_4_235_167->C->Card6+World_4_235_167->C->Card7+
World_4_236_157->A->Card4 + World_4_236_157->B->Card2+World_4_236_157->B->Card3+World_4_236_157->B->Card6 + World_4_236_157->C->Card1+World_4_236_157->C->Card5+World_4_236_157->C->Card7+
World_4_237_156->A->Card4 + World_4_237_156->B->Card2+World_4_237_156->B->Card3+World_4_237_156->B->Card7 + World_4_237_156->C->Card1+World_4_237_156->C->Card5+World_4_237_156->C->Card6+
World_4_256_137->A->Card4 + World_4_256_137->B->Card2+World_4_256_137->B->Card5+World_4_256_137->B->Card6 + World_4_256_137->C->Card1+World_4_256_137->C->Card3+World_4_256_137->C->Card7+
World_4_257_136->A->Card4 + World_4_257_136->B->Card2+World_4_257_136->B->Card5+World_4_257_136->B->Card7 + World_4_257_136->C->Card1+World_4_257_136->C->Card3+World_4_257_136->C->Card6+
World_4_267_135->A->Card4 + World_4_267_135->B->Card2+World_4_267_135->B->Card6+World_4_267_135->B->Card7 + World_4_267_135->C->Card1+World_4_267_135->C->Card3+World_4_267_135->C->Card5+
World_4_356_127->A->Card4 + World_4_356_127->B->Card3+World_4_356_127->B->Card5+World_4_356_127->B->Card6 + World_4_356_127->C->Card1+World_4_356_127->C->Card2+World_4_356_127->C->Card7+
World_4_357_126->A->Card4 + World_4_357_126->B->Card3+World_4_357_126->B->Card5+World_4_357_126->B->Card7 + World_4_357_126->C->Card1+World_4_357_126->C->Card2+World_4_357_126->C->Card6+
World_4_367_125->A->Card4 + World_4_367_125->B->Card3+World_4_367_125->B->Card6+World_4_367_125->B->Card7 + World_4_367_125->C->Card1+World_4_367_125->C->Card2+World_4_367_125->C->Card5+
World_4_567_123->A->Card4 + World_4_567_123->B->Card5+World_4_567_123->B->Card6+World_4_567_123->B->Card7 + World_4_567_123->C->Card1+World_4_567_123->C->Card2+World_4_567_123->C->Card3+
World_5_123_467->A->Card5 + World_5_123_467->B->Card1+World_5_123_467->B->Card2+World_5_123_467->B->Card3 + World_5_123_467->C->Card4+World_5_123_467->C->Card6+World_5_123_467->C->Card7+
World_5_124_367->A->Card5 + World_5_124_367->B->Card1+World_5_124_367->B->Card2+World_5_124_367->B->Card4 + World_5_124_367->C->Card3+World_5_124_367->C->Card6+World_5_124_367->C->Card7+
World_5_126_347->A->Card5 + World_5_126_347->B->Card1+World_5_126_347->B->Card2+World_5_126_347->B->Card6 + World_5_126_347->C->Card3+World_5_126_347->C->Card4+World_5_126_347->C->Card7+
World_5_127_346->A->Card5 + World_5_127_346->B->Card1+World_5_127_346->B->Card2+World_5_127_346->B->Card7 + World_5_127_346->C->Card3+World_5_127_346->C->Card4+World_5_127_346->C->Card6+
World_5_134_267->A->Card5 + World_5_134_267->B->Card1+World_5_134_267->B->Card3+World_5_134_267->B->Card4 + World_5_134_267->C->Card2+World_5_134_267->C->Card6+World_5_134_267->C->Card7+
World_5_136_247->A->Card5 + World_5_136_247->B->Card1+World_5_136_247->B->Card3+World_5_136_247->B->Card6 + World_5_136_247->C->Card2+World_5_136_247->C->Card4+World_5_136_247->C->Card7+
World_5_137_246->A->Card5 + World_5_137_246->B->Card1+World_5_137_246->B->Card3+World_5_137_246->B->Card7 + World_5_137_246->C->Card2+World_5_137_246->C->Card4+World_5_137_246->C->Card6+
World_5_146_237->A->Card5 + World_5_146_237->B->Card1+World_5_146_237->B->Card4+World_5_146_237->B->Card6 + World_5_146_237->C->Card2+World_5_146_237->C->Card3+World_5_146_237->C->Card7+
World_5_147_236->A->Card5 + World_5_147_236->B->Card1+World_5_147_236->B->Card4+World_5_147_236->B->Card7 + World_5_147_236->C->Card2+World_5_147_236->C->Card3+World_5_147_236->C->Card6+
World_5_167_234->A->Card5 + World_5_167_234->B->Card1+World_5_167_234->B->Card6+World_5_167_234->B->Card7 + World_5_167_234->C->Card2+World_5_167_234->C->Card3+World_5_167_234->C->Card4+
World_5_234_167->A->Card5 + World_5_234_167->B->Card2+World_5_234_167->B->Card3+World_5_234_167->B->Card4 + World_5_234_167->C->Card1+World_5_234_167->C->Card6+World_5_234_167->C->Card7+
World_5_236_147->A->Card5 + World_5_236_147->B->Card2+World_5_236_147->B->Card3+World_5_236_147->B->Card6 + World_5_236_147->C->Card1+World_5_236_147->C->Card4+World_5_236_147->C->Card7+
World_5_237_146->A->Card5 + World_5_237_146->B->Card2+World_5_237_146->B->Card3+World_5_237_146->B->Card7 + World_5_237_146->C->Card1+World_5_237_146->C->Card4+World_5_237_146->C->Card6+
World_5_246_137->A->Card5 + World_5_246_137->B->Card2+World_5_246_137->B->Card4+World_5_246_137->B->Card6 + World_5_246_137->C->Card1+World_5_246_137->C->Card3+World_5_246_137->C->Card7+
World_5_247_136->A->Card5 + World_5_247_136->B->Card2+World_5_247_136->B->Card4+World_5_247_136->B->Card7 + World_5_247_136->C->Card1+World_5_247_136->C->Card3+World_5_247_136->C->Card6+
World_5_267_134->A->Card5 + World_5_267_134->B->Card2+World_5_267_134->B->Card6+World_5_267_134->B->Card7 + World_5_267_134->C->Card1+World_5_267_134->C->Card3+World_5_267_134->C->Card4+
World_5_346_127->A->Card5 + World_5_346_127->B->Card3+World_5_346_127->B->Card4+World_5_346_127->B->Card6 + World_5_346_127->C->Card1+World_5_346_127->C->Card2+World_5_346_127->C->Card7+
World_5_347_126->A->Card5 + World_5_347_126->B->Card3+World_5_347_126->B->Card4+World_5_347_126->B->Card7 + World_5_347_126->C->Card1+World_5_347_126->C->Card2+World_5_347_126->C->Card6+
World_5_367_124->A->Card5 + World_5_367_124->B->Card3+World_5_367_124->B->Card6+World_5_367_124->B->Card7 + World_5_367_124->C->Card1+World_5_367_124->C->Card2+World_5_367_124->C->Card4+
World_5_467_123->A->Card5 + World_5_467_123->B->Card4+World_5_467_123->B->Card6+World_5_467_123->B->Card7 + World_5_467_123->C->Card1+World_5_467_123->C->Card2+World_5_467_123->C->Card3+
World_6_123_457->A->Card6 + World_6_123_457->B->Card1+World_6_123_457->B->Card2+World_6_123_457->B->Card3 + World_6_123_457->C->Card4+World_6_123_457->C->Card5+World_6_123_457->C->Card7+
World_6_124_357->A->Card6 + World_6_124_357->B->Card1+World_6_124_357->B->Card2+World_6_124_357->B->Card4 + World_6_124_357->C->Card3+World_6_124_357->C->Card5+World_6_124_357->C->Card7+
World_6_125_347->A->Card6 + World_6_125_347->B->Card1+World_6_125_347->B->Card2+World_6_125_347->B->Card5 + World_6_125_347->C->Card3+World_6_125_347->C->Card4+World_6_125_347->C->Card7+
World_6_127_345->A->Card6 + World_6_127_345->B->Card1+World_6_127_345->B->Card2+World_6_127_345->B->Card7 + World_6_127_345->C->Card3+World_6_127_345->C->Card4+World_6_127_345->C->Card5+
World_6_134_257->A->Card6 + World_6_134_257->B->Card1+World_6_134_257->B->Card3+World_6_134_257->B->Card4 + World_6_134_257->C->Card2+World_6_134_257->C->Card5+World_6_134_257->C->Card7+
World_6_135_247->A->Card6 + World_6_135_247->B->Card1+World_6_135_247->B->Card3+World_6_135_247->B->Card5 + World_6_135_247->C->Card2+World_6_135_247->C->Card4+World_6_135_247->C->Card7+
World_6_137_245->A->Card6 + World_6_137_245->B->Card1+World_6_137_245->B->Card3+World_6_137_245->B->Card7 + World_6_137_245->C->Card2+World_6_137_245->C->Card4+World_6_137_245->C->Card5+
World_6_145_237->A->Card6 + World_6_145_237->B->Card1+World_6_145_237->B->Card4+World_6_145_237->B->Card5 + World_6_145_237->C->Card2+World_6_145_237->C->Card3+World_6_145_237->C->Card7+
World_6_147_235->A->Card6 + World_6_147_235->B->Card1+World_6_147_235->B->Card4+World_6_147_235->B->Card7 + World_6_147_235->C->Card2+World_6_147_235->C->Card3+World_6_147_235->C->Card5+
World_6_157_234->A->Card6 + World_6_157_234->B->Card1+World_6_157_234->B->Card5+World_6_157_234->B->Card7 + World_6_157_234->C->Card2+World_6_157_234->C->Card3+World_6_157_234->C->Card4+
World_6_234_157->A->Card6 + World_6_234_157->B->Card2+World_6_234_157->B->Card3+World_6_234_157->B->Card4 + World_6_234_157->C->Card1+World_6_234_157->C->Card5+World_6_234_157->C->Card7+
World_6_235_147->A->Card6 + World_6_235_147->B->Card2+World_6_235_147->B->Card3+World_6_235_147->B->Card5 + World_6_235_147->C->Card1+World_6_235_147->C->Card4+World_6_235_147->C->Card7+
World_6_237_145->A->Card6 + World_6_237_145->B->Card2+World_6_237_145->B->Card3+World_6_237_145->B->Card7 + World_6_237_145->C->Card1+World_6_237_145->C->Card4+World_6_237_145->C->Card5+
World_6_245_137->A->Card6 + World_6_245_137->B->Card2+World_6_245_137->B->Card4+World_6_245_137->B->Card5 + World_6_245_137->C->Card1+World_6_245_137->C->Card3+World_6_245_137->C->Card7+
World_6_247_135->A->Card6 + World_6_247_135->B->Card2+World_6_247_135->B->Card4+World_6_247_135->B->Card7 + World_6_247_135->C->Card1+World_6_247_135->C->Card3+World_6_247_135->C->Card5+
World_6_257_134->A->Card6 + World_6_257_134->B->Card2+World_6_257_134->B->Card5+World_6_257_134->B->Card7 + World_6_257_134->C->Card1+World_6_257_134->C->Card3+World_6_257_134->C->Card4+
World_6_345_127->A->Card6 + World_6_345_127->B->Card3+World_6_345_127->B->Card4+World_6_345_127->B->Card5 + World_6_345_127->C->Card1+World_6_345_127->C->Card2+World_6_345_127->C->Card7+
World_6_347_125->A->Card6 + World_6_347_125->B->Card3+World_6_347_125->B->Card4+World_6_347_125->B->Card7 + World_6_347_125->C->Card1+World_6_347_125->C->Card2+World_6_347_125->C->Card5+
World_6_357_124->A->Card6 + World_6_357_124->B->Card3+World_6_357_124->B->Card5+World_6_357_124->B->Card7 + World_6_357_124->C->Card1+World_6_357_124->C->Card2+World_6_357_124->C->Card4+
World_6_457_123->A->Card6 + World_6_457_123->B->Card4+World_6_457_123->B->Card5+World_6_457_123->B->Card7 + World_6_457_123->C->Card1+World_6_457_123->C->Card2+World_6_457_123->C->Card3+
World_7_123_456->A->Card7 + World_7_123_456->B->Card1+World_7_123_456->B->Card2+World_7_123_456->B->Card3 + World_7_123_456->C->Card4+World_7_123_456->C->Card5+World_7_123_456->C->Card6+
World_7_124_356->A->Card7 + World_7_124_356->B->Card1+World_7_124_356->B->Card2+World_7_124_356->B->Card4 + World_7_124_356->C->Card3+World_7_124_356->C->Card5+World_7_124_356->C->Card6+
World_7_125_346->A->Card7 + World_7_125_346->B->Card1+World_7_125_346->B->Card2+World_7_125_346->B->Card5 + World_7_125_346->C->Card3+World_7_125_346->C->Card4+World_7_125_346->C->Card6+
World_7_126_345->A->Card7 + World_7_126_345->B->Card1+World_7_126_345->B->Card2+World_7_126_345->B->Card6 + World_7_126_345->C->Card3+World_7_126_345->C->Card4+World_7_126_345->C->Card5+
World_7_134_256->A->Card7 + World_7_134_256->B->Card1+World_7_134_256->B->Card3+World_7_134_256->B->Card4 + World_7_134_256->C->Card2+World_7_134_256->C->Card5+World_7_134_256->C->Card6+
World_7_135_246->A->Card7 + World_7_135_246->B->Card1+World_7_135_246->B->Card3+World_7_135_246->B->Card5 + World_7_135_246->C->Card2+World_7_135_246->C->Card4+World_7_135_246->C->Card6+
World_7_136_245->A->Card7 + World_7_136_245->B->Card1+World_7_136_245->B->Card3+World_7_136_245->B->Card6 + World_7_136_245->C->Card2+World_7_136_245->C->Card4+World_7_136_245->C->Card5+
World_7_145_236->A->Card7 + World_7_145_236->B->Card1+World_7_145_236->B->Card4+World_7_145_236->B->Card5 + World_7_145_236->C->Card2+World_7_145_236->C->Card3+World_7_145_236->C->Card6+
World_7_146_235->A->Card7 + World_7_146_235->B->Card1+World_7_146_235->B->Card4+World_7_146_235->B->Card6 + World_7_146_235->C->Card2+World_7_146_235->C->Card3+World_7_146_235->C->Card5+
World_7_156_234->A->Card7 + World_7_156_234->B->Card1+World_7_156_234->B->Card5+World_7_156_234->B->Card6 + World_7_156_234->C->Card2+World_7_156_234->C->Card3+World_7_156_234->C->Card4+
World_7_234_156->A->Card7 + World_7_234_156->B->Card2+World_7_234_156->B->Card3+World_7_234_156->B->Card4 + World_7_234_156->C->Card1+World_7_234_156->C->Card5+World_7_234_156->C->Card6+
World_7_235_146->A->Card7 + World_7_235_146->B->Card2+World_7_235_146->B->Card3+World_7_235_146->B->Card5 + World_7_235_146->C->Card1+World_7_235_146->C->Card4+World_7_235_146->C->Card6+
World_7_236_145->A->Card7 + World_7_236_145->B->Card2+World_7_236_145->B->Card3+World_7_236_145->B->Card6 + World_7_236_145->C->Card1+World_7_236_145->C->Card4+World_7_236_145->C->Card5+
World_7_245_136->A->Card7 + World_7_245_136->B->Card2+World_7_245_136->B->Card4+World_7_245_136->B->Card5 + World_7_245_136->C->Card1+World_7_245_136->C->Card3+World_7_245_136->C->Card6+
World_7_246_135->A->Card7 + World_7_246_135->B->Card2+World_7_246_135->B->Card4+World_7_246_135->B->Card6 + World_7_246_135->C->Card1+World_7_246_135->C->Card3+World_7_246_135->C->Card5+
World_7_256_134->A->Card7 + World_7_256_134->B->Card2+World_7_256_134->B->Card5+World_7_256_134->B->Card6 + World_7_256_134->C->Card1+World_7_256_134->C->Card3+World_7_256_134->C->Card4+
World_7_345_126->A->Card7 + World_7_345_126->B->Card3+World_7_345_126->B->Card4+World_7_345_126->B->Card5 + World_7_345_126->C->Card1+World_7_345_126->C->Card2+World_7_345_126->C->Card6+
World_7_346_125->A->Card7 + World_7_346_125->B->Card3+World_7_346_125->B->Card4+World_7_346_125->B->Card6 + World_7_346_125->C->Card1+World_7_346_125->C->Card2+World_7_346_125->C->Card5+
World_7_356_124->A->Card7 + World_7_356_124->B->Card3+World_7_356_124->B->Card5+World_7_356_124->B->Card6 + World_7_356_124->C->Card1+World_7_356_124->C->Card2+World_7_356_124->C->Card4+
World_7_456_123->A->Card7 + World_7_456_123->B->Card4+World_7_456_123->B->Card5+World_7_456_123->B->Card6 + World_7_456_123->C->Card1+World_7_456_123->C->Card2+World_7_456_123->C->Card3


}

