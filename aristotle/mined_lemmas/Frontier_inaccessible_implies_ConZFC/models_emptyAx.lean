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

theorem models_emptyAx (h : (∅ : ZFSet.{u}) ∈ A) : (A : Type (u+1)) ⊨ emptyAx := by
  rw [emptyAx]; realize_simp
  exact ⟨∅, h, fun y _ => ZFSet.notMem_empty y⟩

