import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The "centered indicator" of a finite set `S`: the indicator of `S` minus its mean value.
It is orthogonal to the all-ones vector. -/

noncomputable def centeredIndicator (S : Finset V) (i : V) : ℝ :=
  (if i ∈ S then (1 : ℝ) else 0) - S.card / (Fintype.card V)

/-- The centered indicator has zero sum, i.e. it is orthogonal to the all-ones vector. -/
