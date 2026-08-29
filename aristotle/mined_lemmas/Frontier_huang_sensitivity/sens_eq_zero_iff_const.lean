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

lemma sens_eq_zero_iff_const {n : ℕ} (f : (Fin n → Bool) → Bool) :
    sens f = 0 ↔ ∀ x y, f x = f y := by
  constructor
  · intro h
    apply const_of_local
    intro x i
    have hx : sensAt f x = 0 := by
      have hle : sensAt f x ≤ sens f := Finset.le_sup (Finset.mem_univ x)
      omega
    by_contra hne
    have hmem : i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => f (flipAt x i) ≠ f x) := by
      simp [hne]
    rw [Finset.card_eq_zero.1 hx] at hmem
    simp at hmem
  · intro h
    apply Nat.le_zero.1
    apply Finset.sup_le
    intro x _
    simp only [sensAt, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    simp [h (flipAt x i) x]

