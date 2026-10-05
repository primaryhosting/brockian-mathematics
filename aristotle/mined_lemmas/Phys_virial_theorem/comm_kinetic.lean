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

lemma comm_kinetic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x p : ι → Module.End ℂ E) (hbar : ℝ)
    (ccr : ∀ j k, comm (x j) (p k) = (if j = k then (hbar * Complex.I) else 0) • 1)
    (hpp : ∀ j k, p j * p k = p k * p j) :
    comm (∑ j, p j * p j) (∑ k, x k * p k)
      = (-(2 * (hbar * Complex.I))) • ∑ j, p j * p j := by
  rw [comm_sum_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [comm_sum_right]
  have key : ∀ k : ι, comm (p j * p j) (x k * p k)
      = (if j = k then (-(2 * (hbar * Complex.I))) • (p j * p j) else 0) := by
    intro k
    rw [comm_mul_right]
    have h1 : comm (p j * p j) (p k) = 0 := by
      simp only [comm]
      rw [mul_assoc, hpp j k, ← mul_assoc, hpp j k, mul_assoc, sub_self]
    have h2 : comm (p j) (x k) = (if j = k then (-(hbar * Complex.I)) else 0) • 1 := by
      have e : comm (p j) (x k) = - comm (x k) (p j) := by simp only [comm]; noncomm_ring
      rw [e, ccr k j]
      by_cases h : j = k <;> simp [h, eq_comm, ← neg_smul]
    rw [comm_sq_left h2, h1]
    by_cases h : j = k <;> simp [h, mul_comm, Algebra.smul_mul_assoc]
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  simp

/-- Commutator of the potential with the virial generator `G = Σ xₖ pₖ`:
it equals `iħ Σ xₖ Wₖ`, i.e. `iħ (r · ∇V)`. -/
