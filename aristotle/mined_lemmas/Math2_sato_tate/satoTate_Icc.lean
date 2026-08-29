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

lemma satoTate_Icc {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    satoTateMeasure.real (Icc α β) = ∫ t in α..β, satoTateDensity t := by
  have hsub : Icc α β ∩ Icc 0 Real.pi = Icc α β :=
    Set.inter_eq_self_of_subset_left (Set.Icc_subset_Icc hα hβ)
  rw [measureReal_def, satoTate_apply measurableSet_Icc, hsub,
    ← ofReal_integral_eq_lintegral_ofReal continuous_satoTateDensity.integrableOn_Icc
      (Filter.Eventually.of_forall satoTateDensity_nonneg),
    ENNReal.toReal_ofReal, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hαβ]
  exact integral_nonneg fun x => satoTateDensity_nonneg x

/-- **The Sato–Tate law for the Frobenius angles of a non-CM elliptic curve.**

Let `E/ℚ` be an elliptic curve without complex multiplication, and for a prime `p` of good
reduction write `a_p = 2√p · cos θ_p` with `θ p ∈ [0, π]` for the Frobenius angle at `p`
(the Hasse bound `|a_p| ≤ 2√p` guarantees that such an angle exists).  The Sato–Tate theorem
(Taylor, Clozel, Harris, Shepherd-Barron, …) states that the angles `θ p` are equidistributed
with respect to the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`; this is the content of the
hypothesis `SatoTateWeak θ` below, phrased as weak convergence of the empirical distributions
of the angles (i.e. convergence of averages of bounded continuous test functions).

The conclusion is the classical density statement: for `0 ≤ α ≤ β ≤ π` the proportion of primes
`p < X` whose Frobenius angle lies in `[α, β]` converges, as `X → ∞`, to `∫_α^β (2/π) sin²t dt`. -/
