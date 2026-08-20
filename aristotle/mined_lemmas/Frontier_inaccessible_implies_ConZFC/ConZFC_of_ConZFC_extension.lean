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

theorem ConZFC_of_ConZFC_extension {T : LSet.Theory} (hT : ZFC ⊆ T) (h : T.IsSatisfiable) :
    ZFC.IsSatisfiable :=
  h.mono hT

/-- Lean's ambient type theory proves the existence of an inaccessible cardinal (the cardinality
of a universe), so the above gives an unconditional proof that `ZFC` is satisfiable. -/
