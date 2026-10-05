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

theorem eventually_primesBelow_card_ne_zero :
    ∀ᶠ (X : ℕ) in atTop, (Nat.primesBelow X).card ≠ 0 := by
  filter_upwards [eventually_ge_atTop 3] with X hX
  exact Finset.card_ne_zero_of_mem (Nat.mem_primesBelow.2 ⟨by omega, Nat.prime_two⟩)

/-- The Sato–Tate law is exactly the statement that the empirical distributions of the angles
`θ p`, `p < X` prime, converge weakly to the Sato–Tate measure as `X → ∞`. -/
