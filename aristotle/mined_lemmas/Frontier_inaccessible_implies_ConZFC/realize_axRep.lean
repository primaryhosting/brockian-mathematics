import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order

/-! ## The first-order language of set theory -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
inductive memRelSym : ℕ → Type
  | mem : memRelSym 2

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/

theorem realize_axRep {n : ℕ} (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 3) :
    (M ⊨ axRep φ) ↔ ∀ p : Fin n → M, ∀ x : M,
      (∀ z : M, memR z x → ∃! w : M, φ.Realize (Sum.elim default p) ![x, z, w]) →
      ∃ y : M, ∀ z : M, memR z x → ∀ w : M,
        φ.Realize (Sum.elim default p) ![x, z, w] → memR w y := by
  simp [axRep, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_rel₂, BoundedFormula.realize_inf,
    BoundedFormula.realize_bdEqual, BoundedFormula.realize_liftAt_one, memR,
    ExistsUnique]

end Realize

/-! ## Closure properties of `V_ o` -/

section VonNeumann

variable {o : Ordinal.{u}} {x y : ZFSet.{u}}

