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

lemma sum_chi {n : ℕ} (S : Finset (Fin n)) :
    (∑ x : Fin n → Bool, chi S x) = if S = ∅ then (2 : ℤ) ^ n else 0 := by
  have hchi : ∀ x : Fin n → Bool,
      chi S x = ∏ i : Fin n, (if i ∈ S then (if x i then (-1 : ℤ) else 1) else 1) := by
    intro x
    rw [Finset.prod_ite_mem, Finset.univ_inter, chi]
  simp only [hchi]
  rw [← Fintype.piFinset_univ (α := Fin n) (β := fun _ => Bool),
    ← Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
      (fun i b => if i ∈ S then (if b then (-1 : ℤ) else 1) else 1)]
  have hb : ∀ i : Fin n,
      (∑ b : Bool, if i ∈ S then (if b then (-1 : ℤ) else 1) else 1)
        = if i ∈ S then (0 : ℤ) else 2 := by
    intro i
    by_cases h : i ∈ S <;> simp [h]
  simp only [hb]
  by_cases hS : S = ∅
  · subst hS
    simp
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hS
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

