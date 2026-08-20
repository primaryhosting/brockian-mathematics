import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

namespace CycleAux

variable (m : ℕ)

/-- The primitive `(m+3)`-rd root of unity. -/

lemma fvec_eigen :
    (SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ fvec m = fied m • fvec m := by
  funext i
  rw [lap_mulVec, fvec_succ, fvec_pred, Pi.smul_apply, smul_eq_mul, fied, fvec,
    Real.cos_add, Real.cos_sub]
  ring

