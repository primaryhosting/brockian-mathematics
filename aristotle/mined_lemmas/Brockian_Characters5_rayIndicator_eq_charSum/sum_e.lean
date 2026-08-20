import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

lemma sum_e : ∑ c : ZMod 5, e c = 0 := by
  have h : ∑ i ∈ Finset.range 5, omega ^ i = 0 :=
    isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)
  calc ∑ c : ZMod 5, e c = ∑ i ∈ Finset.range 5, omega ^ i := by
        simp only [e]
        exact Finset.sum_nbij' (fun c => c.val) (fun i => (i : ZMod 5))
          (by intro c _; simpa using c.val_lt)
          (by intro i _; exact Finset.mem_univ _)
          (by intro c _; simp [ZMod.natCast_val, ZMod.cast_id])
          (by intro i hi; simp only [Finset.mem_range] at hi
              exact ZMod.val_natCast_of_lt hi)
          (by intro c _; rfl)
    _ = 0 := h

/-- Orthogonality of the character `e`. -/
