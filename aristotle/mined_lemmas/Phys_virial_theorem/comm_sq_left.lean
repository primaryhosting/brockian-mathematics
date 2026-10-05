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

lemma comm_sq_left {A B : Module.End ℂ E} {c : ℂ} (h : comm A B = c • 1) :
    comm (A * A) B = (2 * c) • A := by
  have e : comm (A * A) B = A * comm A B + comm A B * A := by simp only [comm]; noncomm_ring
  rw [e, h]
  simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, two_mul, add_smul]

