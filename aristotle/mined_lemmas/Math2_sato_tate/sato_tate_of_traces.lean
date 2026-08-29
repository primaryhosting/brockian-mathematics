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

theorem sato_tate_of_traces (a : ℕ → ℤ)
    (h : SatoTateWeak fun p => frobeniusAngle (a p) p) {α β : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    Tendsto (fun X : ℕ =>
        (((Nat.primesBelow X).filter fun p => frobeniusAngle (a p) p ∈ Icc α β).card : ℝ) /
          ((Nat.primesBelow X).card : ℝ))
      atTop (𝓝 (∫ t in α..β, (2 / Real.pi) * Real.sin t ^ 2)) :=
  sato_tate _ h hα hαβ hβ


/-! ### The counting form of the Sato–Tate law, and its equivalence with the weak form -/

/-- The proportion of primes `p < X` whose angle `θ p` lies in the set `s`. -/
