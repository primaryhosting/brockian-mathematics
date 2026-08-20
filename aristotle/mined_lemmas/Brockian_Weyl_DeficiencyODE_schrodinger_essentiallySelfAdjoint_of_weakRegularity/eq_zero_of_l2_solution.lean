import Brockian.Weyl.DeficiencyODE

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
# Essential self-adjointness of Schrödinger operators via deficiency indices

This file develops, from scratch:

* a minimal framework for (possibly unbounded) operators on a complex Hilbert space,
  given as a linear map `T : D →ₗ[ℂ] H` out of a submodule `D` of `H`, together with
  their graphs, adjoint graphs, symmetry and essential self-adjointness;
* the *basic criterion* of essential self-adjointness: a densely defined symmetric
  operator whose deficiency spaces `ker (T* ∓ i)` are trivial is essentially
  self-adjoint;
* the deficiency ("Weyl limit point") analysis of the second order difference
  equation attached to a discrete Schrödinger operator, and the resulting
  essential self-adjointness of the discrete Schrödinger operator
  `(T u) n = u (n-1) + u (n+1) + V n * u n` on `ℓ²(ℤ, ℂ)`, defined on the
  (dense) span of the standard basis vectors, for an **arbitrary** real potential
  `V : ℤ → ℝ`.

The main theorem
`schrodinger_essentiallySelfAdjoint_of_weakRegularity` is unconditional: no regularity
(or boundedness) hypothesis on the potential is needed, so the classical weak regularity
assumption is discharged. Everything is proved from first principles on top of Mathlib;
in particular the framework for unbounded operators, their adjoints and essential
self-adjointness is built here.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Brockian.Weyl.DeficiencyODE

/-! ## An abstract framework for unbounded operators -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The graph of an operator `T` defined on the submodule `D` of `H`. -/

theorem eq_zero_of_l2_solution {V : ℤ → ℝ} {z : ℂ} (hz : z.im ≠ 0) {c : ℤ → ℂ}
    (hT : Tendsto c atTop (𝓝 0)) (hB : Tendsto c atBot (𝓝 0))
    (h : ∀ n, c (n - 1) + c (n + 1) + (V n : ℂ) * c n = z * c n) :
    ∀ n, c n = 0 := by
  have hnormsq : ∀ w : ℂ, ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    intro w; rw [Complex.sq_norm]; simp [Complex.normSq_apply]
  set t : ℤ → ℝ := fun n => (wronskian c n).im / (2 * z.im) with ht
  have h2 : (2 : ℝ) * z.im ≠ 0 := by simpa using hz
  have hstep : ∀ n, t n = t (n - 1) + ‖c n‖ ^ 2 := by
    intro n
    have hd := wronskian_diff (V := V) h n
    have him : (wronskian c n).im - (wronskian c (n - 1)).im
        = 2 * z.im * ‖c n‖ ^ 2 := by
      have hh : ((wronskian c n - wronskian c (n - 1)) : ℂ).im
          = ((z - conj z) * (c n * conj (c n))).im := by rw [hd]
      rw [hnormsq]
      simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, Complex.sub_re] at hh ⊢
      linarith [hh]
    show (wronskian c n).im / (2 * z.im)
        = (wronskian c (n - 1)).im / (2 * z.im) + ‖c n‖ ^ 2
    field_simp
    linarith [him]
  have hmono : Monotone t := by
    refine monotone_int_of_le_succ fun n => ?_
    have hs := hstep (n + 1)
    simp only [add_sub_cancel_right] at hs
    nlinarith [sq_nonneg ‖c (n + 1)‖]
  have hconj : Tendsto (fun n => conj (c n)) atTop (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).comp hT
  have hconjB : Tendsto (fun n => conj (c n)) atBot (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).comp hB
  have hshiftT : Tendsto (fun n : ℤ => c (n + 1)) atTop (𝓝 0) :=
    hT.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
  have hshiftB : Tendsto (fun n : ℤ => c (n + 1)) atBot (𝓝 0) :=
    hB.comp (tendsto_atBot_add_const_right _ 1 tendsto_id)
  have hshiftconjT : Tendsto (fun n : ℤ => conj (c (n + 1))) atTop (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).comp hshiftT
  have hshiftconjB : Tendsto (fun n : ℤ => conj (c (n + 1))) atBot (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).comp hshiftB
  have hWT : Tendsto (fun n => wronskian c n) atTop (𝓝 0) := by
    simpa [wronskian] using (hshiftT.mul hconj).sub (hshiftconjT.mul hT)
  have hWB : Tendsto (fun n => wronskian c n) atBot (𝓝 0) := by
    simpa [wronskian] using (hshiftB.mul hconjB).sub (hshiftconjB.mul hB)
  have htT : Tendsto t atTop (𝓝 0) := by
    have := (Complex.continuous_im.tendsto (0 : ℂ)).comp hWT
    simpa [ht] using this.div_const (2 * z.im)
  have htB : Tendsto t atBot (𝓝 0) := by
    have := (Complex.continuous_im.tendsto (0 : ℂ)).comp hWB
    simpa [ht] using this.div_const (2 * z.im)
  have hzero : ∀ n, t n = 0 := by
    intro n
    have hle : t n ≤ 0 := ge_of_tendsto htT (by
      filter_upwards [eventually_ge_atTop n] with m hm using hmono hm)
    have hge : (0 : ℝ) ≤ t n := le_of_tendsto htB (by
      filter_upwards [eventually_le_atBot n] with m hm using hmono hm)
    linarith
  intro n
  have hs := hstep n
  rw [hzero n, hzero (n - 1)] at hs
  have hn0 : ‖c n‖ = 0 := by nlinarith [norm_nonneg (c n)]
  simpa using hn0

end DifferenceEquation

/-! ## The discrete Schrödinger operator -/

section Schrodinger

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the discrete Schrödinger operator: the (dense) span of the basis
vectors, i.e. the finitely supported vectors. -/
