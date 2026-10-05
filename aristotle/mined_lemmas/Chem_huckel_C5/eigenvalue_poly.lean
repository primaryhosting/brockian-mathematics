/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α` is `0` and the resonance integral `β` is `1`). -/

lemma eigenvalue_poly {μ : ℝ} {v : Fin 5 → ℝ} (hv : v ≠ 0) (heq : C5 *ᵥ v = μ • v) :
    μ ^ 3 - μ ^ 2 - 3 * μ + 2 = 0 := by
  have h2 : C5 ^ 2 *ᵥ v = μ ^ 2 • v := by
    rw [pow_two, ← Matrix.mulVec_mulVec, heq, Matrix.mulVec_smul, heq, smul_smul, ← pow_two]
  have h3 : C5 ^ 3 *ᵥ v = μ ^ 3 • v := by
    rw [pow_succ, ← Matrix.mulVec_mulVec, heq, Matrix.mulVec_smul, h2, smul_smul]
    ring_nf
  have hmul : C5 ^ 3 *ᵥ v = (C5 ^ 2 + (3 : ℝ) • C5 - (2 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ)) *ᵥ v := by
    rw [← C5_pow_three]
  rw [h3, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, h2, heq,
    Matrix.one_mulVec] at hmul
  have hkey : (μ ^ 3 - μ ^ 2 - 3 * μ + 2) • v = 0 := by
    ext i
    have hi := congrFun hmul i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
    linear_combination hi
  rcases smul_eq_zero.mp hkey with h | h
  · exact h
  · exact absurd h hv

