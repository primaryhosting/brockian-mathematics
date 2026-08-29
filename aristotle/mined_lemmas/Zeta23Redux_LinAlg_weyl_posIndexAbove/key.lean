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
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped BigOperators

namespace Zeta23Redux.LinAlg

section Aux

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The (real part of the) Hermitian quadratic form `x ↦ x* M x`. -/
private noncomputable def qform (M : Matrix n n ℂ) (x : n → ℂ) : ℝ := (star x ⬝ᵥ M *ᵥ x).re

/-- The squared euclidean norm of a vector. -/
private noncomputable def nsq (x : n → ℂ) : ℝ := (star x ⬝ᵥ x).re

omit [DecidableEq n] in

private lemma key (hA : A.IsHermitian) (hE : E.IsHermitian) (θ : ℝ)
    (hEθ : ∀ i, |hE.eigenvalues i| ≤ θ) (c : Fin d → ℂ)
    (hsupp : ∀ i, c i ≠ 0 → θ < (hA.add hE).eigenvalues i)
    (hker : ∀ j, 0 < hA.eigenvalues j →
      (star ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ
        ((hA.add hE).eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ c) j = 0) :
    c = 0 := by
  classical
  by_contra hc
  set V : Matrix (Fin d) (Fin d) ℂ :=
    ((hA.add hE).eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hV
  set x : Fin d → ℂ := V *ᵥ c with hx
  -- coordinates of `x` in the `(A+E)`-eigenbasis are `c`
  have hVc : star V *ᵥ x = c := by
    rw [hx, Matrix.mulVec_mulVec, hV, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mulVec]
  have hnsqx : nsq x = nsq c := by
    rw [hx, hV, nsq_mulVec]
  -- `x* (A+E) x > θ ‖x‖²`
  have h1 : θ * nsq x < qform (A + E) x := by
    rw [qform_eq_sum (hA.add hE) x, hnsqx, nsq_eq_sum, Finset.mul_sum]
    have hcoord : (star ((hA.add hE).eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) = c :=
      hVc
    rw [hcoord]
    obtain ⟨i0, hi0⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc (funext fun i => h i)
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · rcases eq_or_ne (c i) 0 with h | h
      · simp [h]
      · exact mul_le_mul_of_nonneg_right (le_of_lt (hsupp i h)) (by positivity)
    · have hpos : 0 < ‖c i0‖ ^ 2 := by positivity
      exact mul_lt_mul_of_pos_right (hsupp i0 hi0) hpos
  -- `x* E x ≤ θ ‖x‖²`
  have h2 : qform E x ≤ θ * nsq x :=
    qform_le hE (fun i => (abs_le.mp (hEθ i)).2) x
  -- hence `x* A x > 0`
  have h3 : 0 < qform A x := by
    have := qform_add A E x
    linarith [h1, h2, this]
  -- but the `A`-coordinates of `x` vanish where the eigenvalues are positive, so `x* A x ≤ 0`
  have h4 : qform A x ≤ 0 := by
    rw [qform_eq_sum hA x]
    refine Finset.sum_nonpos fun j _ => ?_
    rcases lt_or_ge 0 (hA.eigenvalues j) with hj | hj
    · have h0 : (star ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x) j = 0 :=
        hker j hj
      rw [h0]
      simp
    · exact mul_nonpos_of_nonpos_of_nonneg hj (by positivity)
  linarith

/-- **Weyl monotonicity / eigenvalue interlacing bound.** If `A` and `E` are Hermitian complex
matrices and every eigenvalue of `E` has absolute value at most `θ`, then the number of
eigenvalues of `A + E` strictly above `θ` is at most the number of strictly positive
eigenvalues of `A`. -/
