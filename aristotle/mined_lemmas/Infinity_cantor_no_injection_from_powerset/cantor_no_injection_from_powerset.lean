import Mathlib

/-!
# Cantor No Injection From Powerset
Category: Frontier — Set Theory
Target: Infinity.cantor_no_injection_from_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- **Dual Cantor theorem**: for any type `X`, no function `g : Set X → X` is injective.

This is exactly Mathlib's `Function.cantor_injective`, which derives it from
`Function.cantor_surjective` via the right inverse
`a ↦ {b | ∀ U, a = g U → U b}`. -/

theorem cantor_no_injection_from_powerset {X : Type*} (g : Set X → X) :
    ¬ Function.Injective g :=
  Function.cantor_injective g

/-- The diagonal set used in the self-contained proof below: the set of points of `X`
that are the `g`-image of some set not containing them. -/
