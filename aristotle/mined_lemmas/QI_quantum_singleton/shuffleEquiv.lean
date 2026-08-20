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

def shuffleEquiv (S T U : Type*) : S × (T × U) ≃ T × S × U :=
  ⟨fun p => (p.2.1, p.1, p.2.2), fun p => (p.2.1, p.1, p.2.2), fun _ => rfl, fun _ => rfl⟩

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Core linear-algebraic form of the quantum Singleton bound.  If `ψ` is a family of `K`
vectors in `α ⊗ β ⊗ γ` satisfying the Knill–Laflamme conditions for the registers `α` and `β`
(the reduced "density matrices" on `α` and on `β` are the same for all codewords and have no
cross terms), then `K ≤ card γ`. -/
