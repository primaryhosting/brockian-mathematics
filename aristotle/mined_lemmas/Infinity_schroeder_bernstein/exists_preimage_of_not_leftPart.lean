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

theorem exists_preimage_of_not_leftPart {x : X} (hx : ¬ leftPart f g x) : ∃ y : Y, g y = x := by
  by_cases h : ∃ y : Y, g y = x
  · exact h
  · exact absurd ⟨0, x, fun y hy => h ⟨y, hy⟩, rfl⟩ hx

open Classical in
/-- The bijection built from the two injections. -/
