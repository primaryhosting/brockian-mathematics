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
Weyl's criterion for equidistribution modulo one, and its application to the
sequence `n ↦ n • α` for irrational `α`.
-/
import Mathlib

open Filter MeasureTheory Metric Set Submodule
open scoped Topology Real

namespace Brockian.Equidistribution

noncomputable section

/-! ## Definitions -/

/-- A sequence `u : ℕ → ℝ` is *equidistributed modulo one* if for every subinterval
`[a, b) ⊆ [0, 1]` the proportion of the first `N` terms whose fractional part lies in `[a, b)`
tends to `b - a`. -/

lemma integral_fourier (n : ℤ) :
    ∫ z : UnitAddCircle, fourier n z = if n = 0 then 1 else 0 := by
  rw [← AddCircle.intervalIntegral_preimage 1 0]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, if_false]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * n) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have hfe : ∀ x : ℝ, (fourier n ((x : ℝ) : UnitAddCircle))
        = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * n) * x) := by
      intro x; rw [fourier_coe_apply]; push_cast; ring_nf
    simp_rw [hfe]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * ((0 : ℝ) + 1 : ℝ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨n, by push_cast; ring⟩
    rw [h1]
    simp

variable (u : ℕ → ℝ)

/-- The Cesàro average of `f` along the sequence `u` viewed on the circle. -/
