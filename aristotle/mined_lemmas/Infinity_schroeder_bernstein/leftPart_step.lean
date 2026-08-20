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

theorem leftPart_step {x : X} (hx : leftPart f g x) : leftPart f g (g (f x)) := by
  obtain ⟨n, z, hz, hzx⟩ := hx
  exact ⟨n + 1, z, hz, by simp [iterateFun, hzx]⟩

