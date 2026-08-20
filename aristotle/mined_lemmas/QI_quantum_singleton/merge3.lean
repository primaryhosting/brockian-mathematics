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

def merge3 (A B : Finset (Fin n)) (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
    (c : {i : Fin n // i ∉ A ∧ i ∉ B} → Fin q) : Fin n → Fin q :=
  fun i => if h : i ∈ A then a ⟨i, h⟩ else if h' : i ∈ B then b ⟨i, h'⟩ else c ⟨i, ⟨h, h'⟩⟩

/-- Splitting the complement of `A` into `B` and the remaining qudits. -/
