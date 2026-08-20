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

namespace Brockian

/-- A `k`-tuple of integers `h : Fin k → ℤ` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture) if for every prime `p` the values
`h 0, …, h (k-1)` do not cover every residue class modulo `p`. -/

def Admissible {k : ℕ} (h : Fin k → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ i, (h i : ZMod p) ≠ r

/-- A tuple of length `k` can never cover all residues modulo a prime `p > k`. -/
