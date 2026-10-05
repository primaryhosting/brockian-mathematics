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

lemma sum_sq_cflip (k : ℕ) (v : Cube k → ℝ) :
    ∑ x : Cube k, ∑ i : Fin k, (v (cflip x i)) ^ 2 = k * ∑ x : Cube k, (v x) ^ 2 := by
  rw [Finset.sum_comm]
  have : ∀ i : Fin k, ∑ x : Cube k, (v (cflip x i)) ^ 2 = ∑ x : Cube k, (v x) ^ 2 :=
    fun i => sum_cflip i (fun x => (v x) ^ 2)
  simp [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

