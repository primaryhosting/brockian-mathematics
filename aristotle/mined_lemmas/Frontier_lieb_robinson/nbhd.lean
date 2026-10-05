/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The `r`-neighbourhood of a set of sites `X` inside a metric space of sites. -/

def nbhd {Site : Type*} [PseudoMetricSpace Site] (r : ℝ) (X : Set Site) : Set Site :=
  {z | ∃ x ∈ X, dist z x ≤ r}

/-- Discrete-time Heisenberg evolution of an observable `a` under `n` layers of local
gates: `evol u v n a = u (n-1) * ⋯ * u 0 * a * v 0 * ⋯ * v (n-1)`. -/
