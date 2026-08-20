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

lemma ip_diffOp_pair_nonneg (i j : Fin k) (v : (Fin k → ZMod 2) → ℝ) :
    0 ≤ ip v (diffOp i (diffOp j v)) := by
  set T : (Fin k → ZMod 2) → ℝ := diffOp i (diffOp j v) with hT
  have h4 : 4 * ip v T = ip T T := by
    have e1 : ip v (fun x => 4 * T x) = 4 * ip v T := ip_const_mul_right 4 v T
    have e2 : ip v (diffOp i (diffOp j T)) = ip (diffOp j (diffOp i v)) T := by
      rw [ip_diffOp_left i v (diffOp j T), ip_diffOp_left j (diffOp i v) T]
    have e3 : diffOp i (diffOp j T) = fun x => 4 * T x := by
      rw [hT]; exact diffOp_pair_sq i j v
    rw [← e1, ← e3, e2, diffOp_comm j i v]
  nlinarith [ip_self_nonneg T, h4]

