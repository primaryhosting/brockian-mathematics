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

lemma rank_flatten_le {Y Z : Type*} [Fintype Y] [Fintype Z] [DecidableEq Y] [DecidableEq Z]
    (f : X → Y → Z → ℂ) :
    (Matrix.of fun (p : X × Y) (z : Z) => f p.1 p.2 z).rank ≤
      (Matrix.of fun (x : X) (p : Y × Z) => f x p.1 p.2).rank *
        (Matrix.of fun (y : Y) (p : X × Z) => f p.1 y p.2).rank := by
  classical
  set FX := Matrix.of fun (x : X) (p : Y × Z) => f x p.1 p.2 with hFX
  set FY := Matrix.of fun (y : Y) (p : X × Z) => f p.1 y p.2 with hFY
  set G := Matrix.of fun (p : X × Y) (z : Z) => f p.1 p.2 z with hG
  obtain ⟨UX, LX, hX⟩ := exists_rank_factor FX
  obtain ⟨UY, LY, hY⟩ := exists_rank_factor FY
  rw [Matrix.mul_assoc] at hX hY
  have hXe : ∀ x y z, ∑ x', (UX * LX) x x' * f x' y z = f x y z := by
    intro x y z
    have h := congrFun (congrFun hX x) (y, z)
    simp only [Matrix.mul_apply, hFX, Matrix.of_apply] at h ⊢
    rw [← h]
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hYe : ∀ x y z, ∑ y', (UY * LY) y y' * f x y' z = f x y z := by
    intro x y z
    have h := congrFun (congrFun hY y) (x, z)
    simp only [Matrix.mul_apply, hFY, Matrix.of_apply] at h ⊢
    rw [← h]
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hPG : ((UX * LX) ⊗ₖ (UY * LY)) * G = G := by
    ext p z
    obtain ⟨x, y⟩ := p
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have key : ∀ x', ∑ y', ((UX * LX) ⊗ₖ (UY * LY)) (x, y) (x', y') * G (x', y') z
        = (UX * LX) x x' * f x' y z := by
      intro x'
      have inner : ∀ y', ((UX * LX) ⊗ₖ (UY * LY)) (x, y) (x', y') * G (x', y') z
          = (UX * LX) x x' * ((UY * LY) y y' * f x' y' z) := by
        intro y'
        simp only [Matrix.kroneckerMap_apply, hG, Matrix.of_apply]
        ring
      rw [Finset.sum_congr rfl fun y' _ => inner y', ← Finset.mul_sum, hYe]
    rw [Finset.sum_congr rfl fun x' _ => key x', hXe]
    rfl
  have hfactor : G = (UX ⊗ₖ UY) * ((LX ⊗ₖ LY) * G) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hPG]
  calc G.rank = ((UX ⊗ₖ UY) * ((LX ⊗ₖ LY) * G)).rank := by rw [← hfactor]
    _ ≤ (UX ⊗ₖ UY).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin FX.rank × Fin FY.rank) := Matrix.rank_le_card_width _
    _ = FX.rank * FY.rank := by simp

/-- The dimension of a product of copies of a fixed submodule. -/
