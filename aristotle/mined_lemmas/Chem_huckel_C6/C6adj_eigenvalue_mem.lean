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

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₆`,
i.e. of the benzene carbon skeleton. -/

theorem C6adj_eigenvalue_mem (μ : ℂ) (v : Fin 6 → ℂ) (hv : v ≠ 0)
    (h : C6adj.mulVec v = μ • v) : μ = 2 ∨ μ = 1 ∨ μ = -1 ∨ μ = -2 := by
  have hpow : ∀ n : ℕ, (C6adj ^ n).mulVec v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
          mul_comm]
  have h4 := hpow 4
  rw [C6adj_pow_four] at h4
  have h2 := hpow 2
  have hsub : ((5 : ℂ) • C6adj ^ 2 - (4 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)).mulVec v
      = ((5 : ℂ) * μ ^ 2 - 4) • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, h2, Matrix.one_mulVec]
    rw [smul_smul, sub_smul]
  rw [hsub] at h4
  have hzero : (μ ^ 4 - ((5 : ℂ) * μ ^ 2 - 4)) • v = 0 := by
    rw [sub_smul, h4, sub_self]
  have hscal : μ ^ 4 - ((5 : ℂ) * μ ^ 2 - 4) = 0 := by
    by_contra hne
    exact hv (by simpa [smul_eq_zero, hne] using hzero)
  have hfac : (μ - 2) * (μ - 1) * (μ + 1) * (μ + 2) = 0 := by
    rw [← hscal]; ring
  rcases mul_eq_zero.1 hfac with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · rcases mul_eq_zero.1 h'' with h₁ | h₁
      · exact Or.inl (by linear_combination h₁)
      · exact Or.inr (Or.inl (by linear_combination h₁))
    · exact Or.inr (Or.inr (Or.inl (by linear_combination h'')))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h')))

/-- **Hückel theory for benzene (C₆).**  A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₆` if and only if `μ = 2 cos (2πk/6)` for some `k ∈ {0,…,5}`. -/
