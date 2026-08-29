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

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) : Type := Fin k → Bool

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/

lemma cflip_cons_zero {k : ℕ} (b : Bool) (y : Cube k) :
    cflip (Fin.cons b y) 0 = Fin.cons (!b) y := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [cflip]
  · intro i
    rw [cflip_of_ne _ (Fin.succ_ne_zero i)]
    simp

