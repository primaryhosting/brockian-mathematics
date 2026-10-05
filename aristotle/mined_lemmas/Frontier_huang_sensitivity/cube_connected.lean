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

lemma cube_connected {n : ℕ} {P : (Fin n → Bool) → Prop} {S : Finset (Fin n)}
    (hstep : ∀ x j, j ∈ S → P x → P (flipAt x j)) :
    ∀ x y, (∀ i, x i ≠ y i → i ∈ S) → P x → P y := by
  have key : ∀ (d : ℕ) (x y : Fin n → Bool),
      ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).card = d →
      (∀ i, x i ≠ y i → i ∈ S) → P x → P y := by
    intro d
    induction d with
    | zero =>
      intro x y hd _ hP
      have hxy : ∀ i, x i = y i := by
        intro i
        by_contra hi
        have hmem : i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i) := by
          simp [hi]
        rw [Finset.card_eq_zero.1 hd] at hmem
        simp at hmem
      rwa [← funext hxy]
    | succ d ih =>
      intro x y hd hS hP
      obtain ⟨i0, hi0⟩ : ∃ i0, x i0 ≠ y i0 := by
        by_contra hcon
        push_neg at hcon
        have hemp : (Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i) = ∅ := by
          simp [hcon]
        rw [hemp] at hd
        simp at hd
      have hxy : flipAt x i0 i0 = y i0 := by
        rw [flipAt_self]
        revert hi0; cases x i0 <;> cases y i0 <;> simp
      have hcard : ((Finset.univ : Finset (Fin n)).filter (fun i => flipAt x i0 i ≠ y i))
          = ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).erase i0 := by
        ext j
        by_cases hj : j = i0
        · subst hj; simp [hxy]
        · simp [hj, flipAt_ne x hj]
      refine ih (flipAt x i0) y ?_ ?_ (hstep x i0 (hS i0 hi0) hP)
      · rw [hcard, Finset.card_erase_of_mem (by simp [hi0]), hd]
        rfl
      · intro i hi
        apply hS
        by_cases hij : i = i0
        · subst hij; exact hi0
        · rwa [flipAt_ne x hij] at hi
  intro x y hS hP
  exact key _ x y rfl hS hP

/-- If no single coordinate flip ever changes the value of `f`, then `f` is constant. -/
