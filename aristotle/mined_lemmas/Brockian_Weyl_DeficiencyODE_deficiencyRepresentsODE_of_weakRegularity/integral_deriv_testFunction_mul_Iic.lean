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

import Brockian.Weyl.WeakDerivative

/-!
# Weyl deficiency spaces are represented by solutions of the Schrödinger ODE

For a continuous potential `q : ℝ → ℝ` and a spectral parameter `z : ℂ`, consider the
formally symmetric differential expression `τ u = -u'' + q u` on the line.  The minimal
operator is the restriction of `τ` to test functions, and the deficiency space at `z`
consists of the `L²` functions `u` which satisfy `τ u = z u` *weakly*, i.e. in the sense
of distributions:

  `∫ u φ'' = ∫ (q - z) u φ`   for all real test functions `φ`.

The main result of this file, `deficiencyRepresentsODE_of_weakRegularity`, states that
this deficiency space coincides with the set of `L²` functions which agree almost
everywhere with a *classical* (twice differentiable) solution of the ODE
`-u'' + q u = z u`.

The nontrivial inclusion is a regularity statement — every weak solution is almost
everywhere a classical solution — which is proved here from scratch (`weakRegularity`)
from the du Bois-Reymond lemmas of `Brockian.Weyl.WeakDerivative`; consequently the final

theorem integral_deriv_testFunction_mul_Iic (hψ : IsTestFunction ψ)
    (hg : Integrable g volume) :
    ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (∫ t in Set.Iic x, g t) = -∫ x : ℝ, (ψ x : ℂ) * g x := by
  have hswap := MeasureTheory.integral_integral_swap (integrable_uncurry_aux hψ hg)
  have hL : ∀ x : ℝ, ∫ t : ℝ, ((deriv ψ x : ℝ) : ℂ) * Set.indicator (Set.Iic x) g t
      = ((deriv ψ x : ℝ) : ℂ) * ∫ t in Set.Iic x, g t := by
    intro x
    rw [integral_const_mul, integral_indicator measurableSet_Iic]
  have hR : ∀ t : ℝ, ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * Set.indicator (Set.Iic x) g t
      = -((ψ t : ℝ) : ℂ) * g t := by
    intro t
    have he : (fun x : ℝ => ((deriv ψ x : ℝ) : ℂ) * Set.indicator (Set.Iic x) g t)
        = Set.indicator (Set.Ici t) (fun x => ((deriv ψ x : ℝ) : ℂ) * g t) := by
      funext x
      by_cases h : t ≤ x <;> simp [Set.indicator, h, Set.mem_Iic, Set.mem_Ici]
    rw [he, integral_indicator measurableSet_Ici, integral_mul_const,
      MeasureTheory.integral_Ici_eq_integral_Ioi, integral_complex_ofReal,
      HasCompactSupport.integral_Ioi_deriv_eq hψ.contDiff_one hψ.2 t]
    push_cast
    ring
  simp only [hL, hR] at hswap
  rw [hswap, ← integral_neg]
  congr 1
  funext t
  ring

/-- Integration by parts for the primitive `x ↦ ∫ t in 0..x, g t` of a locally integrable
function; equivalently, the distributional derivative of the primitive is `g`. -/
