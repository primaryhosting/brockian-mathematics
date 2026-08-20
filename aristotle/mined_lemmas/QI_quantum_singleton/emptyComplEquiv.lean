/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

namespace QI

/-! ## Linear-algebra preliminaries -/

section RankLemmas

variable {X Y : Type*}

/-- Rank–nullity for the linear map `v ↦ M *ᵥ v`. -/

def emptyComplEquiv (n q : ℕ) :
    (Fin n → Fin q) ≃ ({i : Fin n // i ∉ (∅ : Finset (Fin n))} → Fin q) where
  toFun w t := w t.val
  invFun z i := z ⟨i, by simp⟩
  left_inv := by intro w; funext i; rfl
  right_inv := by intro z; funext t; rfl

/-- Erasing no qudit at all is always correctable for an isometric encoding.  In particular the
erasure conditions in `Correctable` are satisfiable, so the Singleton bound below is not
vacuous. -/
