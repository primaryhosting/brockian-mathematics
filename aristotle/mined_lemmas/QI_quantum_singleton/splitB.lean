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

def splitB (S1 S2 : Finset (Fin n)) (hdisj : ∀ i, i ∈ S2 → i ∉ S1) :
    (({i : Fin n // i ∉ S1 ∧ i ∉ S2} → Fin q) × ({i : Fin n // i ∈ S2} → Fin q))
      ≃ ({i : Fin n // i ∉ S1} → Fin q) where
  toFun p := fun t => if h : t.val ∈ S2 then p.2 ⟨t.val, h⟩ else p.1 ⟨t.val, ⟨t.property, h⟩⟩
  invFun z := (fun b => z ⟨b.val, b.property.1⟩, fun c => z ⟨c.val, hdisj c.val c.property⟩)
  left_inv := by
    rintro ⟨b, c⟩
    ext t
    · simp only [t.property.2, dif_neg, not_false_iff]
    · simp only [t.property, dif_pos]
  right_inv := by
    intro z
    funext t
    by_cases h : t.val ∈ S2 <;> simp [h]

/-- Configurations on the complement of `S2` split as (`S1` part) × (middle part). -/
