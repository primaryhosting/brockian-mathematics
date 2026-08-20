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

def infinityAx : LSet.Sentence :=
  ∃' ((∃' ((memF &1 &0) ⊓ (∀' (∼ (memF &2 &1))))) ⊓
    (∀' ((memF &1 &0) ⟹ (∃' ((memF &2 &0) ⊓
      (∀' ((memF &3 &2) ⇔ ((memF &3 &1) ⊔ (&3 =' &1)))))))))

/-- Foundation: every nonempty set has an `∈`-minimal element. -/
