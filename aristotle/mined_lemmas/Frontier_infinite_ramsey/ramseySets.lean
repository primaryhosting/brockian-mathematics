import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
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

open Filter

section RamseyConstruction

/-- Pick an element of a set of naturals (junk value `0` if the set is empty). -/

noncomputable def ramseySets : ℕ → Set ℕ
  | 0 => A
  | n + 1 => ramseySets n ∩ {m | c (pick (ramseySets n)) m = k ∧ pick (ramseySets n) < m}

/-- The monochromatic sequence. -/
