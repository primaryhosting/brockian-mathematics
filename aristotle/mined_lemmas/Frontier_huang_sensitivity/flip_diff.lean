/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Frontier

/-! ## Basic definitions for Boolean functions on the hypercube -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}`, valued in `ℤ`. -/

lemma flip_diff {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1)
    (x : Fin n → Bool) (i : Fin n) :
    2 ^ n * ((if f x then (-1 : ℤ) else 1) - (if f (flipAt x i) then (-1 : ℤ) else 1))
      = 2 * fourierCoeff f {i} * (if x i then (-1 : ℤ) else 1) := by
  rw [mul_sub, ← sum_coeff_mul_chi f x, ← sum_coeff_mul_chi f (flipAt x i),
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single ({i} : Finset (Fin n))]
  · rw [chi_flipAt_of_mem (by simp) x, chi, Finset.prod_singleton]
    ring
  · intro S _ hS
    rcases Nat.lt_or_ge S.card 2 with h2 | h2
    · have hcases : S.card = 0 ∨ S.card = 1 := by omega
      rcases hcases with h | h
      · rw [Finset.card_eq_zero.1 h]
        simp [chi]
      · obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h
        subst hj
        have hij : i ∉ ({j} : Finset (Fin n)) := by
          simp only [Finset.mem_singleton]
          rintro rfl
          exact hS rfl
        rw [chi_flipAt_of_notMem hij x]
        ring
    · rw [coeff_eq_zero_of_two_le_card hdeg h2]; ring
  · intro hc
    exact absurd (Finset.mem_univ _) hc

