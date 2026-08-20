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

lemma mem_smulSubgroup {m : ℕ} {A : Type*} [AddCommGroup A] {a : A} :
    a ∈ smulSubgroup m A ↔ ∃ b : A, m • b = a := Iff.rfl

/-- If `A / H` is finite, then there is a finite set of coset representatives for `H` in `A`. -/
