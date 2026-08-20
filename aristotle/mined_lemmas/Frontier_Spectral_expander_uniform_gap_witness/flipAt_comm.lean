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

lemma flipAt_comm (x : Fin k → ZMod 2) (i j : Fin k) :
    flipAt (flipAt x i) j = flipAt (flipAt x j) i := by
  funext l
  by_cases hi : l = i <;> by_cases hj : l = j
  · subst hi; subst hj; rfl
  · subst hi; rw [flipAt_of_ne _ hj, flipAt_self, flipAt_self, flipAt_of_ne _ hj]
  · subst hj; rw [flipAt_self, flipAt_of_ne _ hi, flipAt_of_ne _ hi, flipAt_self]
  · rw [flipAt_of_ne _ hj, flipAt_of_ne _ hi, flipAt_of_ne _ hi, flipAt_of_ne _ hj]

