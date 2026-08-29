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
open scoped ENNReal NNReal BoundedContinuousFunction

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

namespace Math2

open MeasureTheory Filter Topology Set

/-! ## The Sato–Tate measure -/

/-- The Sato–Tate measure on `ℝ`: the probability measure supported on `[0, π]` with
density `(2/π) · sin²θ` with respect to Lebesgue measure. -/

theorem tendsto_angleEmpiricalProb (θ : ℕ → ℝ) (h : SatoTateLaw θ) :
    Tendsto (fun X : ℕ => angleEmpiricalProb θ X) atTop (𝓝 satoTateProb) :=
  (satoTateLaw_iff_tendsto θ).1 h

/-- **The Sato–Tate distribution of Frobenius angles.**

Let `a : ℕ → ℤ` be the traces of Frobenius of an elliptic curve over `ℚ` without complex
multiplication, and let `θ_p = arccos (a p / (2√p)) ∈ [0, π]` be the associated Frobenius
angles. Granting the Sato–Tate law (the equidistribution statement proved by
Clozel–Harris–Shepherd-Barron–Taylor for such curves), for every subinterval `[α, β]` of
`[0, π]` the proportion of primes `p < X` whose Frobenius angle lies in `[α, β]` converges,
as `X → ∞`, to the Sato–Tate mass

`(2/π) ∫_α^β sin²θ dθ = (sin α cos α - sin β cos β + β - α)/π`. -/
