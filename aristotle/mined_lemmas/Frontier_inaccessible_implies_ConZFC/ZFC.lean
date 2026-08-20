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

def ZFC : LSet.Theory :=
  {extAx, emptyAx, pairAx, unionAx, powerAx, infinityAx, foundationAx, choiceAx}
    ∪ (Set.range fun p : (k : ℕ) × LSet.Formula (Fin k ⊕ Fin 1) => sepAx p.1 p.2)
    ∪ (Set.range fun p : (k : ℕ) × LSet.Formula (Fin k ⊕ Fin 2) => repAx p.1 p.2)

/-! ## Auxiliary simplification lemmas for realization -/

