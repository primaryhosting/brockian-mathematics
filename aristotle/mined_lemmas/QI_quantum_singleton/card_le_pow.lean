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

theorem card_le_pow {d K : ℕ} {ψ : Fin K → ((Fin n → Fin q) → ℂ)} (h : IsQECC n q d K ψ) :
    K ≤ q ^ n := by
  classical
  set Ψ : Matrix (Fin K) (Fin n → Fin q) ℂ := Matrix.of fun i v => ψ i v with hΨ
  have h1 : Ψ * Ψᴴ = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, hΨ,
      Matrix.one_apply, RCLike.star_def]
    exact h.1 i j
  have h2 : Ψ.rank = K := by
    rw [← Matrix.rank_self_mul_conjTranspose, h1, Matrix.rank_one, Fintype.card_fin]
  calc K = Ψ.rank := h2.symm
    _ ≤ Fintype.card (Fin n → Fin q) := Matrix.rank_le_card_width _
    _ = q ^ n := by simp

/-- **Quantum Singleton bound** (additive form): for an `[[n, k, d]]` quantum code with
`k ≥ 1` logical qudits, `2 * (d - 1) + k ≤ n`. -/
