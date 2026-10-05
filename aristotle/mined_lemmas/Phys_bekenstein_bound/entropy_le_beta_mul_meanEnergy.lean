/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset Real

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of energy `E`
contained in a sphere of radius `R`. -/

lemma entropy_le_beta_mul_meanEnergy {ι : Type*} [Fintype ι] (beta : ℝ) (p E : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hZ : ∑ i, Real.exp (-(beta * E i)) ≤ 1) :
    -∑ i, p i * Real.log (p i) ≤ beta * ∑ i, p i * E i := by
  have key : ∀ i : ι, p i * (-(beta * E i) - Real.log (p i))
      ≤ Real.exp (-(beta * E i)) - p i := by
    intro i
    have h := mul_log_sub_log_le_sub (hp i) (Real.exp_pos (-(beta * E i)))
    rwa [Real.log_exp] at h
  have hsum' : ∑ i, p i * (-(beta * E i) - Real.log (p i))
      ≤ ∑ i, (Real.exp (-(beta * E i)) - p i) := Finset.sum_le_sum fun i _ => key i
  rw [Finset.sum_sub_distrib, hsum] at hsum'
  have hexp : ∑ i, p i * (-(beta * E i) - Real.log (p i))
      = -(beta * ∑ i, p i * E i) - ∑ i, p i * Real.log (p i) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hexp] at hsum'
  linarith

/-- **Bekenstein bound.**  For a quantum system confined to a sphere of radius `R`, whose
energy spectrum `E` satisfies the (modular-Hamiltonian) normalization
`∑ᵢ exp (-2πR Eᵢ / (ℏ c)) ≤ 1`, the Gibbs entropy of any state `p` of the system is bounded
by `2 π k R ⟨E⟩ / (ℏ c)`. -/
