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

lemma one_le_rank_of_ne_zero (ρ : Matrix X X ℂ) (h : ρ ≠ 0) : 1 ≤ ρ.rank := by
  by_contra hc
  have h0 : ρ.rank = 0 := by omega
  have hb : LinearMap.range ρ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
  apply h
  ext a a'
  have hmem : ρ.mulVecLin (Pi.single a' 1) ∈ LinearMap.range ρ.mulVecLin := ⟨_, rfl⟩
  rw [hb, Submodule.mem_bot] at hmem
  have := congrFun hmem a
  simpa [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using this

