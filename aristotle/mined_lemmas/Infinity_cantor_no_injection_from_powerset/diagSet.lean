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

def diagSet {X : Type*} (g : Set X → X) : Set X :=
  {x | ∃ U : Set X, g U = x ∧ x ∉ U}

/-- Self-contained diagonal proof of the dual Cantor theorem, not using
`Function.cantor_injective`: if `g : Set X → X` were injective, then `g (diagSet g)`
would belong to `diagSet g` if and only if it does not. -/
