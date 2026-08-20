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

noncomputable def repAx (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 2)) : LSet.Sentence :=
  Formula.iAlls (β := Fin k) (Formula.relabel Sum.inr (∀' (repHyp k φ ⟹ repConcl k φ)))

/-- The first-order theory ZFC, in the language with a single binary relation symbol. -/
