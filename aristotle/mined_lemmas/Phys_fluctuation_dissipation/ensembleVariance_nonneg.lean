/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the required
-- header appears above as a plain block comment and is repeated as a module docstring below.)

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

namespace Phys

variable {ι : Type*} [Fintype ι]

/-- Unnormalized Boltzmann weight of the microstate `i` for the canonical ensemble at inverse
temperature `β`, with unperturbed energy `E i` and the observable `A` coupled to an external
field `f` (perturbed energy `E i - f * A i`). -/

theorem ensembleVariance_nonneg [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) (f : ℝ) :
    0 ≤ ensembleAvg beta E A f (fun i => A i ^ 2) - (ensembleAvg beta E A f A) ^ 2 := by
  have hZpos := partition_pos beta E A f
  have hcs : (∑ i, A i * boltzmann beta E A f i) ^ 2
      ≤ (∑ i, A i ^ 2 * boltzmann beta E A f i) * partition beta E A f :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun i _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (fun i _ => (Real.exp_pos _).le) (fun i _ => by ring)
  have hrw : (∑ i, A i ^ 2 * boltzmann beta E A f i) / partition beta E A f
      - ((∑ i, A i * boltzmann beta E A f i) / partition beta E A f) ^ 2
      = ((∑ i, A i ^ 2 * boltzmann beta E A f i) * partition beta E A f
        - (∑ i, A i * boltzmann beta E A f i) ^ 2) / partition beta E A f ^ 2 := by
    field_simp
  rw [ensembleAvg, ensembleAvg, hrw]
  exact div_nonneg (by linarith) (by positivity)

/-- Positivity of the static response for `β ≥ 0`: the susceptibility is nonnegative. -/
