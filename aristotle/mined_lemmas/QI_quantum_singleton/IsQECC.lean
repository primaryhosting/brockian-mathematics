/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Kronecker ComplexOrder
open Matrix Module

namespace QI

section LinearAlgebra

variable {X W : Type*} [Fintype X] [Fintype W] [DecidableEq X] [DecidableEq W]

/-- Rank factorization: every matrix `F` factors as `U * L * F = F` with `U` having
`F.rank` columns. -/

def IsQECC (n q d K : ℕ) (ψ : Fin K → ((Fin n → Fin q) → ℂ)) : Prop :=
  (∀ i j, ∑ v : Fin n → Fin q, ψ i v * (starRingEnd ℂ) (ψ j v) = if i = j then 1 else 0) ∧
  (∀ S : Finset (Fin n), S.card + 1 ≤ d →
    ∃ ρ : ({i // i ∈ S} → Fin q) → ({i // i ∈ S} → Fin q) → ℂ,
      ∀ i j x y, ∑ z : {i // i ∉ S} → Fin q,
          ψ i (merge S x z) * (starRingEnd ℂ) (ψ j (merge S y z))
        = (if i = j then (1 : ℂ) else 0) * ρ x y)

/-- Configurations on the complement of `∅` are exactly global configurations. -/
