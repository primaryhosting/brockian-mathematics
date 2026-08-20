import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order Set

/-! ## Cardinal arithmetic of the von Neumann hierarchy below an inaccessible -/

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal `κ`, all the beth-numbers are smaller than `κ`. -/

theorem models_pairAx (hpair : ∀ x ∈ A, ∀ y ∈ A, ({x, y} : ZFSet) ∈ A) :
    (A : Type (u+1)) ⊨ pairAx := by
  rw [pairAx]; realize_simp
  intro a ha b hb
  refine ⟨{a, b}, hpair a ha b hb, fun w _ => ?_⟩
  simp

