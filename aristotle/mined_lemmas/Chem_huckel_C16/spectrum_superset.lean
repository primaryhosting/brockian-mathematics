/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ### The shift matrices

`U n` is the matrix of the `n`-fold cyclic shift on `Fin 16`; the adjacency matrix of the
cycle graph `C₁₆` is `U 1 + U 15`. -/

/-- The matrix of the `n`-fold cyclic shift of `Fin 16`. -/

theorem spectrum_superset :
    {z : ℂ | ∃ k : Fin 16, z = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 16)} ⊆
      spectrum ℂ ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) := by
  rintro w ⟨k, rfl⟩
  set m : ℂ := zt ^ (k : ℕ) with hm
  have hm16 : m ^ 16 = 1 := by
    rw [hm, ← pow_mul, mul_comm, pow_mul, zt_pow16, one_pow]
  have hmmod : ∀ n : ℕ, m ^ (n % 16) = m ^ n := by
    intro n
    conv_rhs => rw [← Nat.div_add_mod n 16]
    rw [pow_add, pow_mul, hm16, one_pow, one_mul]
  -- the eigenvalue equals `m + m^15`
  have hlam : (2 * Real.cos (2 * Real.pi * (k : ℕ) / 16) : ℂ) = m + m ^ 15 := by
    have h1 : lamC (k : ℕ) = zt ^ (k : ℕ) + zt ^ (16 - (k : ℕ)) :=
      lamC_eq _ (le_of_lt k.isLt)
    have h2 : zt ^ (16 - (k : ℕ)) = m ^ 15 := by
      have hne : zt ^ (k : ℕ) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
      have e1 : zt ^ (k : ℕ) * zt ^ (16 - (k : ℕ)) = 1 := zt_pow_mul _ (le_of_lt k.isLt)
      have e2 : zt ^ (k : ℕ) * m ^ 15 = 1 := by
        rw [hm, ← pow_mul, ← pow_add]
        have : (k : ℕ) + (k : ℕ) * 15 = 16 * (k : ℕ) := by ring
        rw [this, pow_mul, zt_pow16, one_pow]
      exact mul_left_cancel₀ hne (e1.trans e2.symm)
    rw [← lamC, h1, h2]
  -- the eigenvector
  set v : Fin 16 → ℂ := fun j => m ^ (j : ℕ) with hv
  have hvne : v ≠ 0 := by
    intro h
    have h0 : v 0 = 0 := by rw [h]; rfl
    rw [hv] at h0
    simp at h0
  have hAv : (SimpleGraph.cycleGraph 16).adjMatrix ℂ *ᵥ v = (m + m ^ 15) • v := by
    funext i
    rw [adjMatrix_eq, Matrix.add_mulVec]
    simp only [Pi.add_apply, U_mulVec, hv, Pi.smul_apply, smul_eq_mul]
    rw [hmmod, hmmod, pow_add, pow_add]
    ring
  -- hence `m + m^15` is in the spectrum
  rw [spectrum.mem_iff]
  intro hunit
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
  apply hunit
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hvne, ?_⟩
  rw [Matrix.sub_mulVec, hAv, hlam, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_self]

/-- **Hückel theory for the C₁₆ annulene ring.**  The eigenvalues of the adjacency matrix of the
cycle graph `C₁₆` are exactly the numbers `2·cos(2πk/16)` for `k = 0, …, 15`. -/
