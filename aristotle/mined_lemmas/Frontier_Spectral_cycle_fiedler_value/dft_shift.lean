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

lemma dft_shift (x : Fin (m + 3) → ℂ) (k : Fin (m + 3)) :
    dft m (fun j => x j - x (j + 1)) k = (1 - ee m (-k)) * dft m x k := by
  have hre : ∑ j : Fin (m + 3), x (j + 1) * ee m (j * k)
      = ee m (-k) * ∑ j : Fin (m + 3), x j * ee m (j * k) := by
    have h1 : ∑ j : Fin (m + 3), x (j + 1) * ee m ((j + 1 - 1) * k)
        = ∑ j : Fin (m + 3), x j * ee m ((j - 1) * k) :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin (m + 3))) (fun j => x j * ee m ((j - 1) * k))
    simp only [add_sub_cancel_right] at h1
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hd : (j - 1) * k = j * k + (-k) := by rw [sub_mul, sub_eq_add_neg, one_mul]
    rw [hd, ee_add]
    ring
  simp only [dft, sub_mul, Finset.sum_sub_distrib, hre]
  ring

/-- The discrete Wirtinger inequality for the cycle. -/
