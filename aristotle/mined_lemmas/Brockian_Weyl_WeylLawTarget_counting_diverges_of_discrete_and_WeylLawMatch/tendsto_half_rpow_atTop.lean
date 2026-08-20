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

import Mathlib

/-!
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of points of `S` that are `≤ Λ`. -/

theorem tendsto_half_rpow_atTop {C d : ℝ} (hC : 0 < C) (hd : 0 < d) :
    Tendsto (fun Λ : ℝ => (C / 2) * Λ ^ (d / 2)) atTop atTop :=
  Tendsto.const_mul_atTop (by positivity) (tendsto_rpow_atTop (by linarith))

/--
**Counting diverges, given a discrete spectrum matching a Weyl law.**

If `S ⊆ ℝ` is a discrete spectrum whose counting function satisfies a Weyl law
`counting S Λ ∼ C * Λ ^ (d / 2)` with `C > 0` and `d > 0`, then
the counting function is monotone, diverges to infinity, and `S` is infinite.
-/
