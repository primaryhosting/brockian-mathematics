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

lemma comm_sum_right {ι : Type*} (s : Finset ι) (A : Module.End ℂ E) (g : ι → Module.End ℂ E) :
    comm A (∑ k ∈ s, g k) = ∑ k ∈ s, comm A (g k) := by
  simp only [comm, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

