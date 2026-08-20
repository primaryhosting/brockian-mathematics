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

theorem csbFun_of_not_leftPart {x : X} (hx : ¬ leftPart f g x) : g (csbFun f g x) = x := by
  have h : csbFun f g x = Classical.choose (exists_preimage_of_not_leftPart f g hx) := by
    simp [csbFun, hx]
  rw [h]
  exact Classical.choose_spec (exists_preimage_of_not_leftPart f g hx)

