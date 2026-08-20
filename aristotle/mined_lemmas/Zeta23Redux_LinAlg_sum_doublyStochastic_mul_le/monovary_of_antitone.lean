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

/-
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- Two antitone functions monovary. -/

lemma monovary_of_antitone {n : Type*} [LinearOrder n] {f g : n → ℝ}
    (hf : Antitone f) (hg : Antitone g) : Monovary f g := by
  intro i j h
  have hji : j ≤ i := by
    by_contra hc
    exact absurd (hg (le_of_lt (lt_of_not_ge hc))) (not_le.2 h)
  exact hf hji

/-- For a permutation matrix, the bilinear form `∑ i j, P i j * (μ i * ν j)` is
`∑ i, μ i * ν (σ i)`. -/
