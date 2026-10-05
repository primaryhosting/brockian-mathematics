/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Complex

namespace Math

/-- The two primitive 6-th roots of unity, written explicitly. -/
private noncomputable def zA : ℂ := (1 + Complex.I * (Real.sqrt 3 : ℝ)) / 2
private noncomputable def zB : ℂ := (1 - Complex.I * (Real.sqrt 3 : ℝ)) / 2


private lemma sq_sqrt_three : (((Real.sqrt 3 : ℝ) : ℂ)) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
  norm_num

/-- A complex number is a primitive 6-th root of unity iff it is a root of `X ^ 2 - X + 1`. -/
