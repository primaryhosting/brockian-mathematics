import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open SimpleGraph Matrix Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆`, over `ℂ`
(the Hückel matrix of benzene in units where `α = 0`, `β = 1`). -/

lemma eigenvalue_mem (μ : ℂ) (h : ∃ v : Fin 6 → ℂ, v ≠ 0 ∧ C6 *ᵥ v = μ • v) :
    ∃ k : ℕ, k < 6 ∧ μ = ((lam k : ℝ) : ℂ) := by
  obtain ⟨v, hv, hvA⟩ := h
  have h2 : (C6 * C6) *ᵥ v = (μ ^ 2) • v := by
    rw [← Matrix.mulVec_mulVec, hvA, Matrix.mulVec_smul, hvA, smul_smul]
    ring_nf
  have h4 : (C6 * C6 * (C6 * C6)) *ᵥ v = (μ ^ 4) • v := by
    rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h2, smul_smul]
    ring_nf
  rw [C6_pow_four, Matrix.sub_mulVec, smul_mulVec, smul_mulVec, h2, Matrix.one_mulVec] at h4
  have hzero : (μ ^ 4 - (5 * μ ^ 2 - 4)) • v = 0 := by
    rw [sub_smul, ← h4, smul_smul, sub_smul, sub_self]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (funext hc)
  have hpoly : μ ^ 4 - (5 * μ ^ 2 - 4) = 0 := by
    have := congrFun hzero i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_right hi
  have hfac : (μ - 1) * (μ + 1) * (μ - 2) * (μ + 2) = 0 := by linear_combination hpoly
  rcases mul_eq_zero.mp hfac with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · exact ⟨1, by norm_num, by rw [lam_one]; push_cast; linear_combination h3⟩
      · exact ⟨2, by norm_num, by rw [lam_two]; push_cast; linear_combination h3⟩
    · exact ⟨0, by norm_num, by rw [lam_zero]; push_cast; linear_combination h''⟩
  · exact ⟨3, by norm_num, by rw [lam_three]; push_cast; linear_combination h'⟩

/-- **Hückel theory for benzene (C₆).**  The eigenvalues of the adjacency matrix of the
cycle graph `C₆` are exactly the numbers `2 cos (2πk/6)` for `k = 0, …, 5`:  each of these
numbers is an eigenvalue, and every eigenvalue is of this form. -/
