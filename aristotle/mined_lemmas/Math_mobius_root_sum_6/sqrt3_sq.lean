import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex

namespace Math

/-- One primitive 6-th root of unity: `1/2 + (√3/2) i`. -/

lemma sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  have : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this

