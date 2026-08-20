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

lemma ip_lapOp_nonneg (v : (Fin k → ZMod 2) → ℝ) : 0 ≤ ip v (lapOp k v) := by
  rw [ip_lapOp]
  exact Finset.sum_nonneg fun i _ => ip_diffOp_self_nonneg i v

/-- The key operator inequality `L² ⪰ 2 L`, which forces every nonzero eigenvalue
of the hypercube Laplacian to be at least `2`. -/
