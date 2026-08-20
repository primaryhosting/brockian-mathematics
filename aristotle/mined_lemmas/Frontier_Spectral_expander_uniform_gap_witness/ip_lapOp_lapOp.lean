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

lemma ip_lapOp_lapOp (v : (Fin k → ZMod 2) → ℝ) :
    ip v (lapOp k (lapOp k v)) = ∑ i, ∑ j, ip v (diffOp i (diffOp j v)) := by
  have h : lapOp k (lapOp k v) = fun x => ∑ i, ∑ j, diffOp i (diffOp j v) x := by
    funext x
    rw [lapOp_eq_sum_diffOp]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := diffOp_sum (Finset.univ : Finset (Fin k)) i (fun j => diffOp j v)
    exact congrFun this x
  rw [h]
  simp only [ip, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

