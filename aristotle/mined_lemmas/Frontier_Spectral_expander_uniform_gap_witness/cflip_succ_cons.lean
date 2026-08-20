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

lemma cflip_succ_cons {k : ℕ} (i : Fin k) (b : Bool) (y : Fin k → Bool) :
    cflip i.succ (Fin.cons b y) = Fin.cons b (cflip i y) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [cflip_of_ne (Fin.succ_ne_zero i).symm]
    simp
  · intro j
    simp only [cflip, Function.update_apply, Fin.succ_inj, Fin.cons_succ]

