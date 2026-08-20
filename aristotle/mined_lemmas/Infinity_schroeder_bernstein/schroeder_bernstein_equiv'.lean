/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

universe u v

variable {X : Type u} {Y : Type v}

/-- `Reach f g` is the smallest predicate on `X` containing every element outside the
range of `g` and closed under `x ↦ g (f x)`.  It is the classical "back-and-forth"
set used in the proof of the Cantor–Schröder–Bernstein theorem. -/
inductive Reach (f : X → Y) (g : Y → X) : X → Prop
  | base (x : X) (h : ∀ y, g y ≠ x) : Reach f g x
  | step (x : X) (h : Reach f g x) : Reach f g (g (f x))

variable {f : X → Y} {g : Y → X}

/-- Every element not in `Reach f g` lies in the range of `g`. -/

theorem schroeder_bernstein_equiv' {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (X ≃ Y) :=
  ⟨Equiv.ofBijective (sbMap f g) ⟨sbMap_injective hf, sbMap_surjective hg⟩⟩

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

