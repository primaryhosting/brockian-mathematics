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


lemma eigenvalue_ge_two {k : ℕ} {mu : ℝ} (hmu : mu ≠ 0) {f : Cube k → ℝ} (hf : f ≠ 0)
    (heig : (hypercube k).lapMatrix ℝ *ᵥ f = mu • f) : 2 ≤ mu := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, hat f s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf (hat_eq_zero_imp f hc)
  have h1 : (2 * wt s : ℝ) * hat f s = mu * hat f s := by
    have hl := hat_lap f s
    rw [heig] at hl
    rw [← hl, hat, hat, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : (2 * wt s : ℝ) = mu := mul_right_cancel₀ hs h1
  have h3 : wt s ≠ 0 := by
    intro h
    rw [h] at h2
    simp only [Nat.cast_zero, mul_zero] at h2
    exact hmu h2.symm
  have h4 : (1 : ℝ) ≤ (wt s : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h3
  rw [← h2]
  linarith

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube graph
`Q k` (on `2 ^ k` vertices) equals `2`. Since the bound `2` does not depend on `k`, the family
`(Q k)_{k ≥ 1}` has a uniform spectral gap. -/
