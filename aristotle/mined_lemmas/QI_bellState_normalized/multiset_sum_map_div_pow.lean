import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma multiset_sum_map_div_pow (S : Multiset ℝ) (a : ℝ) (p : ℕ) :
    (S.map (fun s => (s / a) ^ p)).sum = (S.map (· ^ p)).sum / a ^ p := by
  rw [div_eq_mul_inv, ← Multiset.sum_map_mul_right]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => by
    rw [div_pow, div_eq_mul_inv])

/-- Two multisets of positive reals with the same power sums are equal. -/
