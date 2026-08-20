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

lemma ee_neg (a : Fin (m + 3)) : ee m (-a) = (starRingEnd ℂ) (ee m a) := by
  have h1 : ee m a * ee m (-a) = 1 := by rw [← ee_add]; simp [ee_zero]
  have h2 : ee m a * (starRingEnd ℂ) (ee m a) = 1 := by
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, norm_ee]
    norm_num
  exact mul_left_cancel₀ (ee_ne_zero m a) (h1.trans h2.symm)

