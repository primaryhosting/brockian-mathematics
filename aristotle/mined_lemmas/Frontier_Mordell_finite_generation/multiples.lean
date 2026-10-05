import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Classical

/-- Multiplication by `m : ℕ` on an additive commutative group, as a group homomorphism. -/

def multiples (A : Type*) [AddCommGroup A] (m : ℕ) : AddSubgroup A :=
  (nsmulHom A m).range

