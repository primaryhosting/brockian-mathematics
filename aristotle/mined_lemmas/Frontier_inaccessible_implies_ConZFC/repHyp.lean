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

def repHyp (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 2)) : LSet.BoundedFormula (Fin k) 1 :=
  ∀' ∀' ∀' ((memF &1 &0) ⟹
    ((BoundedFormula.relabel (k := 0)
        (Sum.elim (fun a => Sum.inl a) ![Sum.inr 1, Sum.inr 2] : Fin k ⊕ Fin 2 → Fin k ⊕ Fin 4) φ) ⟹
      ((BoundedFormula.relabel (k := 0)
        (Sum.elim (fun a => Sum.inl a) ![Sum.inr 1, Sum.inr 3] : Fin k ⊕ Fin 2 → Fin k ⊕ Fin 4) φ) ⟹
        (&2 =' &3))))

/-- The conclusion of the replacement schema: the image is a set. -/
