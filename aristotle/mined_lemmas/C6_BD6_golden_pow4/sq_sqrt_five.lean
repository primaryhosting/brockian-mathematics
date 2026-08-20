import Mathlib
namespace C6.BD6

/-- `Real.sqrt 5` squared is `5`. -/

private lemma sq_sqrt_five : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

