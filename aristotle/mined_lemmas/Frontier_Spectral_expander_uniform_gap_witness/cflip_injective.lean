/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/

lemma cflip_injective {k : ℕ} (x : Fin k → Bool) :
    Function.Injective (fun i : Fin k => cflip i x) := by
  intro i j h
  by_contra hij
  have h1 : cflip i x i = cflip j x i := congrFun h i
  rw [cflip_self, cflip_of_ne hij] at h1
  simp at h1

/-- Reindexing a sum along the involution `cflip i`. -/
