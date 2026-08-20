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

lemma diffOp_pair_sq (i j : Fin k) (v : (Fin k → ZMod 2) → ℝ) :
    diffOp i (diffOp j (diffOp i (diffOp j v))) =
      fun x => 4 * diffOp i (diffOp j v) x := by
  have h1 : diffOp j (diffOp i (diffOp j v)) = diffOp i (diffOp j (diffOp j v)) := by
    rw [diffOp_comm j i (diffOp j v)]
  rw [h1, diffOp_diffOp_self j v, diffOp_const_mul, diffOp_const_mul,
    diffOp_diffOp_self i (diffOp j v)]
  funext x
  ring

/-! ## The inner product and the spectral gap inequality -/

/-- Inner product of real functions on the cube. -/
