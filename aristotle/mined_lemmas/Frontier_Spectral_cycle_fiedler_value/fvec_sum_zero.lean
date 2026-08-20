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

lemma fvec_sum_zero : ∑ i : Fin (m + 3), fvec m i = 0 := by
  have h1 : ∑ i : Fin (m + 3), fvec m i = (∑ i : Fin (m + 3), ee m ((1 : Fin (m + 3)) * i)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [one_mul, fvec_eq_re]
  rw [h1, sum_ee, if_neg]
  · simp
  · simp

