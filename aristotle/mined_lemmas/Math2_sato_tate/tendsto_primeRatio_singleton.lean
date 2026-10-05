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

lemma tendsto_primeRatio_singleton (θ : ℕ → ℝ) (h : SatoTateCounting θ) {c : ℝ}
    (hc0 : 0 ≤ c) (hcpi : c ≤ Real.pi) :
    Tendsto (fun X => (empirical θ X).real {c}) atTop (𝓝 0) := by
  have hlim := h c c hc0 le_rfl hcpi
  simp only [intervalIntegral.integral_same] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with X hX
  rw [Set.Icc_self, empirical_real θ (card_primesBelow_ne_zero hX) (measurableSet_singleton c),
    primeRatio]

/-- Under the counting form of the Sato–Tate law, the empirical measures of the angles converge
weakly to the Sato–Tate measure. -/
