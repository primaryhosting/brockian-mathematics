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

variable {k : ℕ}

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a point of the discrete cube `(ZMod 2)^k`. -/

lemma lapOp_chi (k : ℕ) (hk : 1 ≤ k) : lapOp k (chi k hk) = (2 : ℝ) • chi k hk := by
  funext x
  simp only [lapOp, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
  · rw [chi_flipAt_first k hk x]; ring
  · intro i _ hi
    rw [chi_flipAt_other k hk x hi]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## Main theorem -/

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian matrix of the
hypercube graph `Q_k` (on `2^k` vertices) is exactly `2`.  Since the bound `2` does not
depend on `k`, the family `(Q_k)` has a uniform spectral gap: uniform-gap graph families
exist. -/
