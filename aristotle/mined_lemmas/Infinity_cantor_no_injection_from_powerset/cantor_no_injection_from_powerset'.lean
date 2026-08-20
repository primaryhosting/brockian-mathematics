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

theorem cantor_no_injection_from_powerset' {X : Type*} (g : Set X → X) :
    ¬ Function.Injective g := by
  intro hg
  set A : Set X := diagSet g with hA
  set a : X := g A with ha
  have key : a ∈ A ↔ a ∉ A := by
    constructor
    · rintro ⟨U, hU, hUa⟩
      have : U = A := hg (hU.trans ha)
      exact this ▸ hUa
    · intro h
      exact ⟨A, ha.symm, h⟩
  exact (iff_not_self key).elim

/-- Consequence: there is no bijection between `Set X` and `X`. -/
