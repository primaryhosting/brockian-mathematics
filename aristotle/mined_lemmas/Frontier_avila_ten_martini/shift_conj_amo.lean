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

theorem shift_conj_amo (lam alpha theta : ℝ) :
    shift 1 * amo lam alpha theta * shift (-1) = amo lam alpha (theta + alpha) := by
  ext u n
  have hpot : amoPot lam alpha theta (n + 1) = amoPot lam alpha (theta + alpha) n := by
    unfold amoPot
    congr 2
    push_cast
    ring
  simp only [ContinuousLinearMap.mul_apply, amo_apply, shift_apply, hpot]
  ring_nf

/-- The spectrum of the almost Mathieu operator is invariant under the phase translation
`θ ↦ θ + α`. -/
