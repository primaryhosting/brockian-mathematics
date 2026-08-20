import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

theorem CosTraceNorm1279_sharp {n : ℕ} :
    traceNorm (cosMatrix (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (0 : ℝ))) = n := by
  refine le_antisymm (CosTraceNorm1279 _ _) ?_
  have hbdd : BddAbove (pairings (cosMatrix (fun _ : Fin n => (0 : ℝ))
      (fun _ : Fin n => (0 : ℝ)))) := by
    refine bddAbove_pairings_of_decomp _ (fun i => Real.cos 0) (fun j => Real.cos 0)
      (fun i => Real.sin 0) (fun j => Real.sin 0) ?_
    ext i j
    simp [cosMatrix]
  have hmem : (n : ℝ) ∈ pairings (cosMatrix (fun _ : Fin n => (0 : ℝ))
      (fun _ : Fin n => (0 : ℝ))) := by
    refine ⟨Matrix.of fun _ _ : Fin n => (1 / n : ℝ), isContraction_allOnes, ?_⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have hn' : (n : ℝ) ≠ 0 := by positivity
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, cosMatrix,
      sub_zero, Real.cos_zero, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  exact le_csSup hbdd hmem

end Brockian

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

