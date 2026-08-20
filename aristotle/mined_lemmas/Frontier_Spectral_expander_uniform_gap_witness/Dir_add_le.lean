/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

/-! ## The hypercube graph -/

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2


lemma Dir_add_le {k : ℕ} (g h : Cube k → ℝ) :
    Dir k (g + h) / 2 ≤ Dir k g + Dir k h := by
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), Dir, Dir, Dir, ← Finset.sum_add_distrib,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg ((g x - g (flipAt i x)) - (h x - h (flipAt i x)))]

/-- Splitting a sum over the `(k+1)`-cube along the first coordinate. -/
