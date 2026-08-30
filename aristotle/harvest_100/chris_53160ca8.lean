/-
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: verified (axioms: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any doc comment `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import Mathlib

namespace Infinity

/-- **Cantor–Schröder–Bernstein**: if there are injections `f : X → Y` and `g : Y → X`,
then there is a bijection between `X` and `Y`.

The proof invokes Mathlib's `Function.Embedding.schroeder_bernstein`. -/
theorem schroeder_bernstein {X Y : Type*} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (X ≃ Y) := by
  obtain ⟨h, hh⟩ := Function.Embedding.schroeder_bernstein hf hg
  exact ⟨Equiv.ofBijective h hh⟩

/-- Embedding form: `X ↪ Y` and `Y ↪ X` give `X ≃ Y`. -/
theorem schroeder_bernstein_embedding {X Y : Type*} (e₁ : X ↪ Y) (e₂ : Y ↪ X) :
    Nonempty (X ≃ Y) :=
  schroeder_bernstein e₁.injective e₂.injective

end Infinity

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

