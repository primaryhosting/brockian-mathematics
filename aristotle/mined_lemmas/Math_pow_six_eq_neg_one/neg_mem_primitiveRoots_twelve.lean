import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- If `z` is a primitive `12`-th root of unity in `ℂ`, then `z ^ 6 = -1`. -/

lemma neg_mem_primitiveRoots_twelve {z : ℂ} (hz : z ∈ primitiveRoots 12 ℂ) :
    -z ∈ primitiveRoots 12 ℂ := by
  rw [mem_primitiveRoots (by norm_num)] at hz ⊢
  have h6 : z ^ 6 = -1 := pow_six_eq_neg_one hz
  have h7 : z ^ 7 = -z := by
    calc z ^ 7 = z ^ 6 * z := by ring
      _ = -z := by rw [h6]; ring
  have h := hz.pow_of_coprime 7 (by norm_num)
  rwa [h7] at h

/-- **Möbius root sum for `n = 12`.**
The sum of the primitive `12`-th roots of unity in `ℂ` equals `μ 12` (which is `0`,
since `12 = 2 ^ 2 * 3` is not squarefree). -/
