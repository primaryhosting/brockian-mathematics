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

def Correctable (V : Matrix (Fin n → Fin q) (Fin K) ℂ) (S : Finset (Fin n)) : Prop :=
  ∃ σ : Matrix ({i : Fin n // i ∈ S} → Fin q) ({i : Fin n // i ∈ S} → Fin q) ℂ,
    ∀ (i j : Fin K) (x y : {i : Fin n // i ∈ S} → Fin q),
      (∑ z : {i : Fin n // i ∉ S} → Fin q, V (glue S x z) i * conj (V (glue S y z) j))
        = (if i = j then (1 : ℂ) else 0) * σ x y

/-- Configurations on the complement of the empty set are just configurations. -/
