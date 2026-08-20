/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

namespace Frontier

/-! ## The multiplication-by-`m` subgroup and its quotient -/

/-- Multiplication by `m` as an endomorphism of an additive commutative group. -/

lemma nsmulHom_apply (m : ℕ) {A : Type*} [AddCommGroup A] (a : A) :
    nsmulHom m A a = m • a := rfl

/-- The subgroup `mA = { m • a | a ∈ A }` of an additive commutative group `A`. -/
