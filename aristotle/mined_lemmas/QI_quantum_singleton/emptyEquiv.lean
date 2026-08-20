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

def emptyEquiv : ({i : Fin n // i ∉ (∅ : Finset (Fin n))} → Fin q) ≃ (Fin n → Fin q) where
  toFun z := fun i => z ⟨i, by simp⟩
  invFun v := fun j => v j
  left_inv z := rfl
  right_inv v := rfl

/-- Sanity check: the hypotheses of the quantum Singleton bound are satisfiable.  The whole
space of `n` qudits, with the standard basis as codewords, is a code of distance at least `1`
with `q ^ n` codewords. -/
