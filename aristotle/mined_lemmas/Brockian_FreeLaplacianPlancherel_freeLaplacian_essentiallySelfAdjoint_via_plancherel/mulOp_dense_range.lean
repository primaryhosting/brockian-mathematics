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

lemma mulOp_dense_range (c : ℂ) (hre : c.re = 0) (him : 1 ≤ |c.im|) :
    Dense (Set.range fun f : mulDomain m hm μ => mulOp m hm μ f + c • (f : Lp ℂ 2 μ)) := by
  refine dense_range_of_orthogonal_trivial _ c (fun z hz => ?_)
  have hden : ∀ x, 1 ≤ ‖(m x : ℂ) + c‖ := by
    intro x
    refine him.trans ?_
    have h := Complex.abs_im_le_norm ((m x : ℂ) + c)
    simpa using h
  have hne : ∀ x, ((m x : ℂ) + c) ≠ 0 := by
    intro x hx
    have h := hden x
    rw [hx] at h
    simp at h
    linarith
  have hb1 : ∀ x, ‖((m x : ℂ) + c)⁻¹‖ ≤ 1 := by
    intro x
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (hden x)
  have hb2 : ∀ x, ‖(m x : ℂ) * ((m x : ℂ) + c)⁻¹‖ ≤ 1 := by
    intro x
    rw [norm_mul, norm_inv, mul_comm, ← div_eq_inv_mul,
      div_le_one (lt_of_lt_of_le zero_lt_one (hden x))]
    have h := Complex.abs_re_le_norm ((m x : ℂ) + c)
    simpa [hre] using h
  obtain ⟨w, hw1, hw2⟩ := exists_mem_mulDomain m hm μ (fun x => ((m x : ℂ) + c)⁻¹)
    (by fun_prop) z hb1 hb2
  have hkey : mulOp m hm μ w + c • (w : Lp ℂ 2 μ) = z := by
    refine lp_ext_of_ae_eq ?_
    filter_upwards [Lp.coeFn_add (mulOp m hm μ w) (c • (w : Lp ℂ 2 μ)),
      Lp.coeFn_smul c (w : Lp ℂ 2 μ), hw1, hw2] with x e1 e2 e3 e4
    rw [e1]
    simp only [Pi.add_apply, e2, Pi.smul_apply, e3, e4, smul_eq_mul]
    have hfac : (m x : ℂ) * ((m x : ℂ) + c)⁻¹ * z x + c * (((m x : ℂ) + c)⁻¹ * z x)
        = (((m x : ℂ) + c) * ((m x : ℂ) + c)⁻¹) * z x := by ring
    rw [hfac, mul_inv_cancel₀ (hne x), one_mul]
  have hzero := hz w
  rw [hkey] at hzero
  exact inner_self_eq_zero.mp hzero

/-- The maximal multiplication operator by a real measurable function is essentially
self-adjoint (in fact self-adjoint). -/
