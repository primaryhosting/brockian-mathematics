/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The doubling endomorphism `P ↦ 2 • P` of an additive commutative group. -/

def doubleHom (A : Type*) [AddCommGroup A] : A →+ A :=
  AddMonoidHom.mk' (fun a => (2 : ℕ) • a) (by intro a b; simp [smul_add])

@[simp]
