import Mathlib
namespace Brockian.MsBinet


private lemma sq_sqrt5 : Real.sqrt 5 ^ 2 = 5 := by
  rw [sq, Real.mul_self_sqrt (by norm_num)]

