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

def eB (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    (({i // i ∈ A} → Fin q) × ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q)) ≃
      ({i : Fin n // i ∉ B} → Fin q) where
  toFun p := fun i => if h : (i : Fin n) ∈ A then p.1 ⟨i, h⟩ else p.2 ⟨i, ⟨h, i.2⟩⟩
  invFun z := (fun j => z ⟨j, Finset.disjoint_left.mp hAB j.2⟩, fun j => z ⟨j, j.2.2⟩)
  left_inv := by
    rintro ⟨a, c⟩
    ext j
    · simp
    · simp [j.2.1]
  right_inv := by
    intro z
    funext i
    by_cases h : (i : Fin n) ∈ A <;> simp [h]

