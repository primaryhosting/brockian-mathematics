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

theorem weakRegularity {q : ℝ → ℝ} (hq : Continuous q) {z : ℂ} {u : ℝ → ℂ}
    (hu : LocallyIntegrable u volume) (hweak : WeakSolution q z u) :
    ∃ v : ℝ → ℂ, ClassicalSolution q z v ∧ u =ᵐ[volume] v := by
  obtain ⟨v, hvc, hae⟩ := exists_continuous_ae_eq_of_weakSolution hq hu hweak
  exact ⟨v, classicalSolution_of_continuous_weakSolution hq hvc (hweak.congr_ae hae), hae⟩

/-- **The deficiency space is represented by the ODE.**  For a continuous potential `q`
and any `z : ℂ`, the deficiency space at `z` — the `L²` distributional solutions of
`-u'' + q u = z u` — consists exactly of the `L²` functions that agree almost everywhere
with a classical solution of that ODE.  The regularity hypothesis is discharged by
`weakRegularity`, so the statement is unconditional. -/
