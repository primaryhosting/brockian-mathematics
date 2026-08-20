import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem prime_iff_dvd_factorial (p : ℕ) : Nat.Prime p ↔ (1 < p ∧ p ∣ ((p - 1)! + 1)) := by
  constructor
  · intro hp
    have hne : NeZero p := ⟨hp.ne_zero⟩
    refine ⟨hp.one_lt, ?_⟩
    have h := (Nat.prime_iff_fac_equiv_neg_one (n := p) hp.ne_one).1 hp
    have h0 : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by push_cast [h]; ring
    exact (ZMod.natCast_eq_zero_iff _ _).1 h0
  · rintro ⟨h1, h2⟩
    have hne : NeZero p := ⟨by omega⟩
    refine (Nat.prime_iff_fac_equiv_neg_one (n := p) (by omega)).2 ?_
    have h0 : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h2
    push_cast at h0
    linear_combination h0

/-- Primality is a Diophantine predicate (Wilson's theorem). -/
