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

private theorem integrable_uncurry_aux (hψ : IsTestFunction ψ) (hg : Integrable g volume) :
    Integrable (Function.uncurry
      (fun x t : ℝ => ((deriv ψ x : ℝ) : ℂ) * Set.indicator (Set.Iic x) g t))
      (volume.prod volume) := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hunc : (Function.uncurry
      (fun x t : ℝ => ((deriv ψ x : ℝ) : ℂ) * Set.indicator (Set.Iic x) g t))
      = Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1}
          (fun p => ((deriv ψ p.1 : ℝ) : ℂ) * g p.2) := by
    funext p
    by_cases h : p.2 ≤ p.1 <;> simp [Function.uncurry, Set.indicator, h, Set.mem_Iic]
  rw [hunc]
  exact (Integrable.mul_prod
    ((Complex.continuous_ofReal.comp hψ.deriv'.continuous).integrable_of_hasCompactSupport
      (hψ.deriv'.2.comp_left (g := Complex.ofReal) (by simp))) hg).indicator hmeas

/-- The integrand appearing in the integration by parts formula for a primitive is
integrable. -/
