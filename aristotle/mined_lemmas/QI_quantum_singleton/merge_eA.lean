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

lemma merge_eA (A B : Finset (Fin n)) (hAB : Disjoint A B) (a : {i // i ∈ A} → Fin q)
    (b : {i // i ∈ B} → Fin q) (c : {i : Fin n // i ∉ A ∧ i ∉ B} → Fin q) :
    merge A a (eA A B hAB (b, c)) = merge3 A B a b c := by
  funext i
  by_cases h : i ∈ A
  · simp [merge, merge3, h]
  · by_cases h' : i ∈ B <;> simp [merge, merge3, eA, h, h']

