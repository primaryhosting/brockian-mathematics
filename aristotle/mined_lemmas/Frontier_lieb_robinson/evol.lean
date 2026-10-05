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

def evol {A : Type*} [Ring A] (u v : ℕ → A) : ℕ → A → A
  | 0, a => a
  | (k + 1), a => u k * evol u v k a * v k

section

variable {Site : Type*} [PseudoMetricSpace Site] {A : Type*} [NormedRing A]

