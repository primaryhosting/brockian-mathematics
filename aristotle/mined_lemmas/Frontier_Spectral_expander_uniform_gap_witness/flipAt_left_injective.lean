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

open Finset Matrix

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a point of the discrete cube `Fin k → Bool`. -/

lemma flipAt_left_injective {k : ℕ} (x : Fin k → Bool) :
    Function.Injective (fun i : Fin k => flipAt i x) := by
  intro i j h
  by_contra hij
  have h1 := congrFun h i
  simp only [flipAt_apply_self, flipAt_apply_of_ne hij] at h1
  simp at h1

/-- The `k`-dimensional hypercube graph `Q_k`: vertices are points of `Fin k → Bool`
and two vertices are adjacent when they differ in exactly one coordinate. -/
