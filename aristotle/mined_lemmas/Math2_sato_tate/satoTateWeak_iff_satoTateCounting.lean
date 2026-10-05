/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

theorem satoTateWeak_iff_satoTateCounting (θ : ℕ → ℝ) (hmem : ∀ p, θ p ∈ Icc 0 Real.pi) :
    SatoTateWeak θ ↔ SatoTateCounting θ := by
  constructor
  · intro h α β hα hαβ hβ
    have hlim := sato_tate θ h hα hαβ hβ
    simp only [satoTateDensity]
    exact hlim.congr' (Eventually.of_forall fun X => by simp only [primeRatio]; congr!)
  · intro h f
    have hconv := tendsto_empiricalProb_of_counting θ hmem h
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hconv
    have := hconv f
    simp only [empiricalProb_toMeasure, satoTateProb_toMeasure] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with X hX
    exact integral_empirical θ f (card_primesBelow_ne_zero hX)


/-! ### Moments of the Sato–Tate distribution

Writing `a_p = 2√p cos θ_p`, the first two moments of the Sato–Tate distribution say that
`a_p / √p` has average `0` and `a_p² / p` has average `1`. -/

