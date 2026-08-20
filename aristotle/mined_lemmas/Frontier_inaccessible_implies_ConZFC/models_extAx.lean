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

theorem models_extAx (hA : A.IsTransitive) : (A : Type (u+1)) ⊨ extAx := by
  rw [extAx]; realize_simp
  intro a ha b hb h
  apply ZFSet.ext
  intro z
  exact ⟨fun hz => (h z (hA a ha hz)).1 hz, fun hz => (h z (hA b hb hz)).2 hz⟩

