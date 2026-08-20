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

def glue (S : Finset (Fin n)) (x : {i : Fin n // i ∈ S} → Fin q)
    (z : {i : Fin n // i ∉ S} → Fin q) : Fin n → Fin q :=
  fun t => if h : t ∈ S then x ⟨t, h⟩ else z ⟨t, h⟩

/-- The Knill–Laflamme erasure-correction condition for the set `S` of qudits:
the partial trace over the complement of `S` of `|ψᵢ⟩⟨ψⱼ|` equals `δᵢⱼ σ` for a fixed
matrix `σ`, i.e. the qudits in `S` carry no information about the encoded state. -/
