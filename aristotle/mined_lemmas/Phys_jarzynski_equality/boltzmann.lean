/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
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

namespace Phys

section Jarzynski

variable {α : Type*} [Fintype α]

/-- The canonical (Boltzmann) partition function at inverse temperature `β` for the
energy function `E` on a finite state space. -/

noncomputable def boltzmann (β : ℝ) (E : α → ℝ) (i : α) : ℝ :=
  Real.exp (-β * E i) / partitionFunction β E

/-- The partition function of a finite system is strictly positive. -/
