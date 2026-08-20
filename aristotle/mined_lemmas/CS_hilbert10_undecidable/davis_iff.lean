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

theorem davis_iff (p q : Poly (Option α ⊕ Fin n))
    (hq0 : ∀ w, 0 ≤ q w) (hqp : ∀ w, |p w| ≤ q w)
    (hqm : ∀ w w' : Option α ⊕ Fin n → ℕ, (∀ i, w i ≤ w' i) → q w ≤ q w')
    (v : α → ℕ) (y : ℕ) :
    (∀ k < y, ∃ t : Fin n → ℕ, p (Sum.elim (Option.elim' k v) t) = 0) ↔
      ∃ (u K : ℕ) (a : Fin n → ℕ), davisCond p q v y u K a :=
  ⟨cond_of_davis p q v y, fun ⟨_, _, _, hC⟩ => davis_of_cond p q hq0 hqp hqm v y _ _ _ hC⟩

/-! ### Bounded universal quantification is Diophantine -/

/-- Index type for the extra variables of Davis' construction: the three scalars `y`, `u`, `K`
followed by the `n` witness variables. -/
abbrev davisIdx (n : ℕ) : Type := Option (Option (Option (Fin n)))

/-- **Bounded universal quantification** preserves Diophantine sets. -/
