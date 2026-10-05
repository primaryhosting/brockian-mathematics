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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The `i`-th standard basis vector of the cube (the string with a single `1` in place `i`). -/

lemma sum_eq_zero_of_eigen {k : ℕ} {μ : ℝ} {v : Cube k → ℝ}
    (hμ : μ ≠ 0) (hv : (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) :
    ∑ x : Cube k, v x = 0 := by
  have h1 : ∑ x : Cube k, ((hypercube k).lapMatrix ℝ *ᵥ v) x = 0 := by
    simp only [lapMatrix_hypercube_mulVec_apply]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_sum_shift v, sub_self]
  rw [hv] at h1
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h1
  exact (mul_eq_zero.mp h1).resolve_left hμ

/-- The parity function of the first coordinate is an eigenvector with eigenvalue `2`. -/
