/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (only Lean's prelude is available), because a
module doc comment such as the header above cannot legally precede an `import` line.
Everything below is therefore developed from scratch: the Cantor–Schröder–Bernstein
back-and-forth construction and its correctness proof.  The only classical ingredient
used is `Classical.choice`.

A Mathlib-flavoured restatement, phrased with `Equiv` (`X ≃ Y`), is derived from the
main theorem in `RequestProject/SchroederBernsteinEquiv.lean`.
-/

namespace Infinity

universe u v

section
variable {X : Type u} {Y : Type v}

/-- `iterate F n x` is the `n`-fold application `F (F (… (F x)))`. -/

theorem schroeder_bernstein {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ (h : X → Y) (k : Y → X),
      Function.Injective h ∧ Function.Surjective h ∧
        (∀ x, k (h x) = x) ∧ (∀ y, h (k y) = y) := by
  have hinj : Function.Injective (bij f g) := bij_injective hf
  have hsurj : Function.Surjective (bij f g) := bij_surjective hg
  refine ⟨bij f g, fun y => Classical.choose (hsurj y), hinj, hsurj, ?_, ?_⟩
  · intro x
    exact hinj (Classical.choose_spec (hsurj (bij f g x)))
  · intro y
    exact Classical.choose_spec (hsurj y)

end
end Infinity

import Mathlib
import RequestProject.SchroederBernstein

/-!
# Schroeder Bernstein, phrased with `Equiv`

A Mathlib-flavoured corollary of `Infinity.schroeder_bernstein`: injections in both
directions yield an equivalence of types `X ≃ Y`.
-/

namespace Infinity

/-- Cantor–Schröder–Bernstein, stated as the existence of an equivalence `X ≃ Y`. -/
