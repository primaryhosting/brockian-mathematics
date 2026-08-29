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

/-!
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Topology
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.Weyl.WeylLawTarget

/-- The spectral counting function of an eigenvalue sequence `lam : ℕ → ℝ`:
`spectralCounting lam Λ` is the number of indices `n` with `lam n ≤ Λ`
(taken as `0` when that index set is infinite). -/

def SpectrumDiscrete (lam : ℕ → ℝ) : Prop :=
  ∀ Λ : ℝ, {n : ℕ | lam n ≤ Λ}.Finite

/-- Weyl-law asymptotics of exponent `d` with (positive) Weyl constant `C`:
`spectralCounting lam Λ / Λ ^ (d / 2) → C` as `Λ → ∞`. -/
