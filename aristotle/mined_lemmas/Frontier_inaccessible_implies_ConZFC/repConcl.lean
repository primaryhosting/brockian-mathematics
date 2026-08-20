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

def repConcl (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 2)) : LSet.BoundedFormula (Fin k) 1 :=
  ∃' ∀' ((memF &2 &1) ⇔ (∃' ((memF &3 &0) ⊓
    (BoundedFormula.relabel (k := 0)
      (Sum.elim (fun a => Sum.inl a) ![Sum.inr 3, Sum.inr 2] : Fin k ⊕ Fin 2 → Fin k ⊕ Fin 4) φ))))

/-- The instance of the replacement schema for a formula `φ` with `k` parameters and two further
free variables. -/
