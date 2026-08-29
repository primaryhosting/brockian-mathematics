/-
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- A finite set `H` of natural numbers is *relatively large* when it has a least element `a`
and its cardinality is at least `a`. -/

def IsRelativelyLarge (H : Finset ℕ) : Prop :=
  ∃ a ∈ H, (∀ b ∈ H, a ≤ b) ∧ a ≤ H.card

/-- `H` is homogeneous of colour `i` for the colouring `c`, at "dimension" `n`: every
`n`-element subset of `H` gets colour `i`. -/
