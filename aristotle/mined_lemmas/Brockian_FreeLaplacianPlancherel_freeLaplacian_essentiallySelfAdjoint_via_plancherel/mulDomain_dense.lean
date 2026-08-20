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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex
open scoped Real ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-! ## Essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A densely defined symmetric operator `T` with domain `D` in a complex Hilbert space is
*essentially self-adjoint* when both deficiency spaces are trivial, i.e. when the ranges of
`T + i` and `T - i` are dense. -/

lemma mulDomain_dense :
    Dense ((mulDomain m hm μ : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) := by
  refine dense_of_orthogonal_trivial (fun z hz => ?_)
  have hb1 : ∀ x, ‖(((1 + (m x) ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (m x)])
  have hb2 : ∀ x, ‖(m x : ℂ) * (((1 + (m x) ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    intro x
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (show (0:ℝ) < (1 + (m x) ^ 2)⁻¹ by positivity), mul_comm, ← div_eq_inv_mul,
      div_le_one (by positivity)]
    nlinarith [sq_abs (m x), sq_nonneg (|m x| - 1)]
  obtain ⟨w, hw, -⟩ := exists_mem_mulDomain m hm μ
    (fun x => (((1 + (m x) ^ 2)⁻¹ : ℝ) : ℂ)) (by fun_prop) z hb1 hb2
  exact eq_zero_of_weighted_inner_eq_zero (u := fun x => (1 + (m x) ^ 2)⁻¹) z (w : Lp ℂ 2 μ)
    (fun x => by positivity) hw (hz _ w.2)

