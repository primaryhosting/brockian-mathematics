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

def leftPart (x : X) : Prop :=
  ∃ n : Nat, ∃ z : X, (∀ y : Y, g y ≠ z) ∧ iterateFun (fun t => g (f t)) n z = x

