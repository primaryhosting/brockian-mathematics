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

def splitA (S1 S2 : Finset (Fin n)) (hdisj : ∀ i, i ∈ S1 → i ∉ S2) :
    (({i : Fin n // i ∈ S1} → Fin q) × ({i : Fin n // i ∉ S1 ∧ i ∉ S2} → Fin q))
      ≃ ({i : Fin n // i ∉ S2} → Fin q) where
  toFun p := fun t => if h : t.val ∈ S1 then p.1 ⟨t.val, h⟩ else p.2 ⟨t.val, ⟨h, t.property⟩⟩
  invFun z := (fun a => z ⟨a.val, hdisj a.val a.property⟩, fun b => z ⟨b.val, b.property.2⟩)
  left_inv := by
    rintro ⟨a, b⟩
    ext t
    · simp only [t.property, dif_pos]
    · simp only [t.property.1, dif_neg, not_false_iff]
  right_inv := by
    intro z
    funext t
    by_cases h : t.val ∈ S1 <;> simp [h]

