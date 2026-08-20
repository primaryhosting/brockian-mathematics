/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

universe u v

section CSB

variable {X : Type u} {Y : Type v}

/-- `iterateFun F n x` is the `n`-fold application of `F` to `x`. -/

def iterateFun (F : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => F (iterateFun F n x)

variable (f : X → Y) (g : Y → X)

/-- The "left part" of `X` in the Schröder-Bernstein construction: those points reachable
from a point outside the range of `g` by iterating `g ∘ f`. -/
