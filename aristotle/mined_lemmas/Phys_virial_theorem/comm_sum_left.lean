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

lemma comm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ E) (B : Module.End ℂ E) :
    comm (∑ j ∈ s, f j) B = ∑ j ∈ s, comm (f j) B := by
  simp only [comm, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

/-- Commutator of the (unnormalised) kinetic term with the virial generator
`G = Σ xₖ pₖ`: it equals `-2iħ Σ pⱼ²`. -/
