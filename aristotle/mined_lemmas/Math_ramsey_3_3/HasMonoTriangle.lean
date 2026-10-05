/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
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

set_option grind.warning false

namespace Math

/-- A 2-colouring `C` of the edges of the complete graph on `Fin n` has a monochromatic
triangle if there are three distinct vertices all of whose connecting edges receive the
same colour. -/

def HasMonoTriangle {n : ℕ} (C : Fin n → Fin n → Bool) : Prop :=
  ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ C a b = C a c ∧ C a b = C b c

/-- Pigeonhole: among five objects coloured with two colours, three share a colour. -/
