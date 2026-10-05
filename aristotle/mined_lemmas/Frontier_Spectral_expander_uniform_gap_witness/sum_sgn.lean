/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-! ### Arithmetic in `ZMod 2` -/


lemma sum_sgn {k : ℕ} (s : Cube k) : ∑ i, sgn (s i) = (k : ℝ) - 2 * wt s := by
  classical
  have h : ∀ i : Fin k, sgn (s i) = 1 - 2 * (if s i ≠ 0 then (1 : ℝ) else 0) := by
    intro i
    by_cases hi : s i = 0
    · simp [sgn, hi]
    · simp [sgn, hi]
      norm_num
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole]
  simp [wt]

/-- `χ_s` is an eigenvector of the hypercube Laplacian with eigenvalue `2 * wt s`. -/
