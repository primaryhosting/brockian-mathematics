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

lemma rank_smul_of_ne_zero {c : ℂ} (hc : c ≠ 0) (ρ : Matrix X X ℂ) :
    (c • ρ).rank = ρ.rank := by
  have h1 : (c • ρ) = (c • (1 : Matrix X X ℂ)) * ρ := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [h1]
  refine Matrix.rank_mul_eq_right_of_isUnit_det _ _ ?_
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact (isUnit_iff_ne_zero).2 (pow_ne_zero _ hc)

end LinearAlgebra

section Core

/-- Reindexing equivalence used to compare flattenings of a three-index array. -/
