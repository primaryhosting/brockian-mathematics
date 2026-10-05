import Mathlib

/-!
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A primitive 8-th root of unity satisfies `z ^ 4 = -1`. -/

lemma pow_five_eq_neg {z : ℂ} (hz : IsPrimitiveRoot z 8) : z ^ 5 = -z := by
  have h := pow_four_eq_neg_one hz
  linear_combination z * h

/-- The sum of the primitive 8-th roots of unity equals `μ 8`. -/
