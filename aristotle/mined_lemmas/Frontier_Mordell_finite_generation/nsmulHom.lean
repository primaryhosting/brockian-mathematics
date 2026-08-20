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

def nsmulHom (m : ℕ) (A : Type*) [AddCommGroup A] : A →+ A :=
  AddMonoidHom.mk' (fun a => m • a) (fun a b => smul_add m a b)

@[simp]
