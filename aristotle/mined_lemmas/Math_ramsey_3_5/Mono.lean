import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Ramsey

/-- A `b`-monochromatic set of vertices for the edge colouring `c`. -/

def Mono (c : ℕ → ℕ → Bool) (b : Bool) (t : Finset ℕ) : Prop :=
  ∀ x ∈ t, ∀ y ∈ t, x ≠ y → c x y = b

/-- The arrow relation: any colouring of the edges on the vertex set `s` contains
either a `true`-coloured clique of size `p` or a `false`-coloured clique of size `q`. -/
