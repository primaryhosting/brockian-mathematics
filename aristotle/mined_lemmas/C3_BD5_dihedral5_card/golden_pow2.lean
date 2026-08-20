import Mathlib
namespace C3.BD5

/-- The dihedral group of order 10 (symmetries of the regular pentagon) has 10 elements. -/

theorem golden_pow2 : ((1+Real.sqrt 5)/2)^2 = ((1+Real.sqrt 5)/2)+1 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

/-- The golden ratio satisfies `φ³ = 2φ + 1`. -/
