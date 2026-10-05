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

lemma degree_le_one_of_sens_le_one {n : ℕ} {f : (Fin n → Bool) → Bool} (hsens : sens f ≤ 1) :
    degree f ≤ 1 := by
  have hsx : ∀ x, sensAt f x ≤ 1 := fun x =>
    le_trans (Finset.le_sup (f := sensAt f) (Finset.mem_univ x)) hsens
  by_cases hconst : ∀ x y, f x = f y
  · have h0 : degree f = 0 := (degree_eq_zero_iff_const f).2 hconst
    omega
  · obtain ⟨x0, i0, hx0⟩ : ∃ x i, f (flipAt x i) ≠ f x := by
      by_contra hc
      push_neg at hc
      exact hconst (const_of_local hc)
    have hstep : ∀ z j, j ∈ (Finset.univ : Finset (Fin n)) →
        (f (flipAt z i0) ≠ f z) → (f (flipAt (flipAt z j) i0) ≠ f (flipAt z j)) := by
      intro z j _ hz
      by_cases hj : j = i0
      · subst hj
        rw [flipAt_flipAt]
        exact fun h => hz h.symm
      · have h1 : f (flipAt z j) = f z := by
          by_contra hh
          exact hj (Finset.card_le_one.1 (hsx z) j (by simp [hh]) i0 (by simp [hz]))
        have hz' : f (flipAt (flipAt z i0) i0) ≠ f (flipAt z i0) := by
          rw [flipAt_flipAt]
          exact fun h => hz h.symm
        have h2 : f (flipAt (flipAt z i0) j) = f (flipAt z i0) := by
          by_contra hh
          exact hj (Finset.card_le_one.1 (hsx (flipAt z i0)) j (by simp [hh]) i0 (by simp [hz']))
        rw [flipAt_comm, h2, h1]
        exact hz
    have hall : ∀ x, f (flipAt x i0) ≠ f x := fun x =>
      cube_connected (P := fun z => f (flipAt z i0) ≠ f z) hstep x0 x (by simp) hx0
    have hinv : ∀ k, k ≠ i0 → ∀ x, f (flipAt x k) = f x := by
      intro k hk x
      by_contra hh
      exact hk (Finset.card_le_one.1 (hsx x) k (by simp [hh]) i0 (by simp [hall x]))
    apply Finset.sup_le
    intro S hS
    simp only [Finset.mem_filter] at hS
    apply Finset.card_le_one.2
    intro a ha b hb
    have hkey : ∀ k ∈ S, k = i0 := by
      intro k hk
      by_contra hne
      exact hS.2 (coeff_eq_zero_of_invariant (hinv k hne) hk)
    rw [hkey a ha, hkey b hb]

/-! ## The verified small cases -/

/-- Huang's inequality `deg f ≤ s(f)^2`, together with `s(f) ≤ deg(f)^2`, verified
for every Boolean function of three variables. -/
