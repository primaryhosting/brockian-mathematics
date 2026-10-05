/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Boltzmann weight `e^{-β H(i)}` of the microstate `i`. -/

lemma sq_thermalAvg_le (β : ℝ) (H A : ι → ℝ) :
    thermalAvg β H A ^ 2 ≤ thermalAvg β H (fun i => A i ^ 2) := by
  have hZ : 0 < partitionFn β H := partitionFn_pos β H
  have hcs : (∑ i, A i * gibbsWeight β H i) ^ 2
      ≤ (∑ i, gibbsWeight β H i) * ∑ i, A i ^ 2 * gibbsWeight β H i := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun i _ => le_of_lt (Real.exp_pos _))
      (fun i _ => mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _)))
      (fun i _ => by simp only [gibbsWeight]; ring)
  rw [thermalAvg, thermalAvg, div_pow, div_le_div_iff₀ (by positivity) hZ]
  calc (∑ i, A i * gibbsWeight β H i) ^ 2 * partitionFn β H
      ≤ ((∑ i, gibbsWeight β H i) * ∑ i, A i ^ 2 * gibbsWeight β H i) * partitionFn β H :=
        mul_le_mul_of_nonneg_right hcs hZ.le
    _ = (∑ i, A i ^ 2 * gibbsWeight β H i) * partitionFn β H ^ 2 := by
        rw [partitionFn]; ring

/-- Self-response form of the fluctuation–dissipation theorem: the susceptibility of an
observable `A` to its own conjugate field is `β` times the equilibrium variance of `A`. -/
