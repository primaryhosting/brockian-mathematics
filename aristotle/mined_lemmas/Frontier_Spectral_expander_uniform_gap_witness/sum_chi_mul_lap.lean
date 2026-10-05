/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The `i`-th standard basis vector of the cube (the string with a single `1`, at `i`). -/

lemma sum_chi_mul_lap {k : ℕ} (S : Cube k) (v : Cube k → ℝ) :
    ∑ x, chi S x * ((hypercube k).lapMatrix ℝ *ᵥ v) x
      = (2 * wt S : ℝ) * ∑ x, chi S x * v x := by
  have step : ∀ i : Fin k, ∑ x : Cube k, chi S x * v (x + basisVec i)
      = sgn (S i) * ∑ x, chi S x * v x := by
    intro i
    have e : ∑ x : Cube k, chi S x * v (x + basisVec i)
        = ∑ y : Cube k, chi S (y + basisVec i) * v y := by
      refine Fintype.sum_equiv (Equiv.addRight (basisVec i)) _ _ ?_
      intro y
      simp only [Equiv.coe_addRight]
      congr 1
      rw [add_assoc, cube_add_self, add_zero]
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [chi_shift]
    ring
  calc ∑ x, chi S x * ((hypercube k).lapMatrix ℝ *ᵥ v) x
      = ∑ x : Cube k, (k * (chi S x * v x) - ∑ i, chi S x * v (x + basisVec i)) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [lap_mulVec_apply, mul_sub, Finset.mul_sum]
        ring
    _ = (k : ℝ) * (∑ x, chi S x * v x) - ∑ i : Fin k, ∑ x : Cube k, chi S x * v (x + basisVec i) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_comm]
    _ = (k : ℝ) * (∑ x, chi S x * v x) - (∑ i, sgn (S i)) * ∑ x, chi S x * v x := by
        rw [Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => step i
    _ = (2 * wt S : ℝ) * ∑ x, chi S x * v x := by
        rw [sum_sgn]; ring

/-! ### Main results -/

