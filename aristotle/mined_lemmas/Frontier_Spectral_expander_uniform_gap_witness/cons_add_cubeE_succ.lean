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

lemma cons_add_cubeE_succ {k : ℕ} (a : ZMod 2) (y : Cube k) (j : Fin k) :
    Fin.cons a y + cubeE j.succ = Fin.cons a (y + cubeE j) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [cubeE, (Fin.succ_ne_zero j).symm]
  · intro m; simp [cubeE, Pi.single_apply, Fin.succ_inj]

/-- Tensorization of the Dirichlet energy along the first coordinate. -/
