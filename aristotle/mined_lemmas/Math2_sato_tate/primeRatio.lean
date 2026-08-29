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

noncomputable def primeRatio (θ : ℕ → ℝ) (s : Set ℝ) (X : ℕ) : ℝ :=
  (((Nat.primesBelow X).filter fun p => θ p ∈ s).card : ℝ) / ((Nat.primesBelow X).card : ℝ)

/-- The Sato–Tate law in its classical "counting" form: for `0 ≤ α ≤ β ≤ π`, the proportion of
primes `p < X` with `θ p ∈ [α, β]` tends to `∫_α^β (2/π) sin²t dt`. -/
