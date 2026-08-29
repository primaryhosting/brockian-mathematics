import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

/-! ## A recursive description of the permanent

`pm M l C` is the weighted count of bijections from the rows listed in `l` onto the
column set `C`, where the weight of a bijection is the product of the corresponding
matrix entries.  It is a convenient recursive handle on the permanent. -/

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommSemiring R]

/-- Weighted count of the bijections from the rows in the list `l` onto the columns in `C`. -/

theorem permanent_zeroOne_eq_card (M : Matrix ι ι ℕ) (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) :
    M.permanent =
      ((Finset.univ : Finset (Equiv.Perm ι)).filter (fun σ => ∀ i, M i (σ i) = 1)).card := by
  rw [permanent_eq_sum_perm, Finset.card_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : ∀ i, M i (σ i) = 1
  · rw [if_pos h, Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const_one]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((h01 i (σ i)).resolve_right hi)

/-! ## Permanents and ring homomorphisms

Valiant's reduction produces a matrix with small *negative* entries; those are removed by
computing modulo a large number.  The following two lemmas are the algebraic content of
that step. -/

