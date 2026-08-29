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

lemma comm_smul_left (c : ℂ) (A B : Module.End ℂ E) : comm (c • A) B = c • comm A B := by
  simp only [comm, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]

