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

lemma cflip_cons_succ {k : ℕ} (b : Bool) (y : Cube k) (i : Fin k) :
    cflip (Fin.cons b y) i.succ = Fin.cons b (cflip y i) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [cflip_of_ne _ (Fin.succ_ne_zero i).symm]
    simp
  · intro j'
    rcases eq_or_ne j' i with rfl | hne
    · rw [cflip_self]
      simp
    · rw [cflip_of_ne _ (fun hc => hne (Fin.succ_injective _ hc))]
      simp [cflip_of_ne y hne]

/-- The Dirichlet energy of the `(k+1)`-cube splits along the first coordinate. -/
