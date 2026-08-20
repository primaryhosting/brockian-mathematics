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

theorem nonempty_equiv_of_injective {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (X ≃ Y) := by
  obtain ⟨h, hinj, hsurj⟩ := schroeder_bernstein hf hg
  exact ⟨Equiv.ofBijective h ⟨hinj, hsurj⟩⟩

/-- The same statement as Mathlib's `Function.Embedding.antisymm`, for comparison. -/
