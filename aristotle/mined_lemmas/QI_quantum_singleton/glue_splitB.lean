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

lemma glue_splitB (S1 S2 : Finset (Fin n)) (hdisj : ∀ i, i ∈ S2 → i ∉ S1)
    (a : {i : Fin n // i ∈ S1} → Fin q) (b : {i : Fin n // i ∉ S1 ∧ i ∉ S2} → Fin q)
    (c : {i : Fin n // i ∈ S2} → Fin q) :
    glue S1 a (splitB S1 S2 hdisj (b, c)) = merge3 S1 S2 a b c := by
  funext t
  by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2 <;> simp [glue, merge3, splitB, h1, h2]

