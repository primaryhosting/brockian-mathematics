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

theorem schroeder_bernstein {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : X → Y, Function.Injective h ∧ Function.Surjective h :=
  ⟨sbMap f g, sbMap_injective hf, sbMap_surjective hg⟩

end Infinity

import Mathlib
import RequestProject.SchroederBernstein

/-!
# Schroeder–Bernstein, Mathlib form

A restatement of `Infinity.schroeder_bernstein` in terms of Mathlib's `Equiv`,
obtained from `Function.Embedding.antisymm` (which is built on
`Function.Embedding.schroeder_bernstein`).
-/

namespace Infinity

/-- **Cantor–Schröder–Bernstein**, Mathlib form: injections both ways give an equivalence. -/
