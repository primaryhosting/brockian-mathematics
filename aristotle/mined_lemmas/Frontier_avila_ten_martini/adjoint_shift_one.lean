/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The complex Hilbert space `ℓ²(ℤ)`, on which the almost Mathieu operator acts. -/
abbrev Hl2 := lp (fun _ : ℤ => ℂ) 2

/-- Auxiliary: the real exponent attached to `p = 2`. -/

theorem adjoint_shift_one : ContinuousLinearMap.adjoint (shift (1 : ℤ)) = shift (-1) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have := (Equiv.addRight (-1 : ℤ)).tsum_eq
    (fun n : ℤ => (inner ℂ ((u : ℤ → ℂ) n) ((shift (1 : ℤ) v : ℤ → ℂ) n) : ℂ))
  simpa [sub_add_cancel, add_comm] using this

