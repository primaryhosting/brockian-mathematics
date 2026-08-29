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


private lemma primitiveRoots_six : primitiveRoots 6 ℂ = {zA, zB} := by
  ext z
  rw [mem_primitiveRoots (by norm_num), isPrimitiveRoot_six_iff]
  have hfac : z ^ 2 - z + 1 = (z - zA) * (z - zB) := by
    unfold zA zB
    linear_combination (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq
      + (-1 / 4 : ℂ) * sq_sqrt_three
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero, Finset.mem_insert, Finset.mem_singleton]

/-- The sum of the primitive 6-th roots of unity equals `μ 6`. -/
