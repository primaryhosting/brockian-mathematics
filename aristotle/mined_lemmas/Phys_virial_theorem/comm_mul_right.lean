import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The commutator `[A, B] = AB - BA` of two linear operators on `E`. -/

lemma comm_mul_right (A B C : Module.End ℂ E) :
    comm A (B * C) = B * comm A C + comm A B * C := by
  simp only [comm]; noncomm_ring

/-- If `[A, B]` is a scalar `c`, then `[A², B] = 2c • A`. -/
