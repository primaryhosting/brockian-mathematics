import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

section Setup

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Partition function of the energy landscape `E k` at inverse temperature `beta`. -/

theorem crooks_theorem_mul (hDB : DetailedBalance E T beta) (hbeta : beta ≠ 0) :
    forwardProb E T beta N x
      = Real.exp (beta * (work E N x - freeEnergyDiff E beta N)) *
          reverseProb E T beta N (reversePath N x) := by
  have hZ0 := partitionFn_pos E beta 0
  have hZN := partitionFn_pos E beta N
  have hexp := exp_neg_beta_freeEnergyDiff E beta N hbeta
  have h0 : reversePath N x 0 = x N := by simp [reversePath]
  rw [reverseProb, h0, reverse_prod_eq, prod_reverse_kernels hDB, sum_energy_telescope]
  rw [forwardProb]
  have hsplit : Real.exp (beta * (work E N x - freeEnergyDiff E beta N))
      = Real.exp (beta * work E N x) * Real.exp (-beta * freeEnergyDiff E beta N) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit, hexp]
  have hE : Real.exp (-beta * (work E N x + E 0 (x 0) - E N (x N)))
      = (Real.exp (beta * work E N x))⁻¹ *
        (Real.exp (-beta * E 0 (x 0)) * (Real.exp (-beta * E N (x N)))⁻¹) := by
    rw [← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hE]
  field_simp

/-- **Crooks fluctuation theorem**: `P_F(γ) / P_R(γ̄) = e^{β(W(γ) − ΔF)}`,
for a microscopically reversible (detailed-balance) protocol on a finite state space. -/
