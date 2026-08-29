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

lemma comm_potential {ι : Type*} [Fintype ι]
    (x W p : ι → Module.End ℂ E) (V : Module.End ℂ E) (hbar : ℝ)
    (hVx : ∀ j, V * x j = x j * V)
    (hVp : ∀ j, comm V (p j) = (hbar * Complex.I) • W j) :
    comm V (∑ k, x k * p k) = (hbar * Complex.I) • ∑ k, x k * W k := by
  rw [comm_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [comm_mul_right, hVp k]
  have h0 : comm V (x k) = 0 := by simp only [comm, hVx k, sub_self]
  rw [h0]
  simp [Algebra.mul_smul_comm]

/-- Expectation value of a commutator with the Hamiltonian vanishes in a stationary state. -/
