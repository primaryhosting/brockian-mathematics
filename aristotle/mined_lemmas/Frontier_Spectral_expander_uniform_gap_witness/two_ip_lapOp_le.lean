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

lemma two_ip_lapOp_le (v : (Fin k → ZMod 2) → ℝ) :
    2 * ip v (lapOp k v) ≤ ip v (lapOp k (lapOp k v)) := by
  rw [ip_lapOp, ip_lapOp_lapOp, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hdiag : 2 * ip v (diffOp i v) = ip v (diffOp i (diffOp i v)) := by
    rw [diffOp_diffOp_self i v, ip_const_mul_right]
  rw [hdiag]
  exact Finset.single_le_sum (f := fun j => ip v (diffOp i (diffOp j v)))
    (fun j _ => ip_diffOp_pair_nonneg i j v) (Finset.mem_univ i)

/-! ## An eigenvector for the eigenvalue 2 -/

/-- The parity character in the first coordinate: an eigenvector of the Laplacian
of `Q_k` with eigenvalue `2`. -/
