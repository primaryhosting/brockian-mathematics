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

theorem csbFun_of_leftPart {x : X} (hx : leftPart f g x) : csbFun f g x = f x := by
  simp [csbFun, hx]

