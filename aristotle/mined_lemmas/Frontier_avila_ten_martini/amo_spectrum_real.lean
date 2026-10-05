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

theorem amo_spectrum_real (lam alpha theta : ℝ) {z : ℂ} (hz : z ∈ spectrum ℂ (amo lam alpha theta)) :
    z = ((z.re : ℝ) : ℂ) := by
  have him : z.im = 0 := (amo_isSelfAdjoint lam alpha theta).im_eq_zero_of_mem_spectrum hz
  exact Complex.ext rfl (by simpa using him)

instance : Nontrivial Hl2 :=
  ⟨⟨lp.single 2 (0 : ℤ) 1, 0, by
      intro h
      have := congrFun (congrArg (fun x : Hl2 => (x : ℤ → ℂ)) h) 0
      simp [lp.single_apply] at this⟩⟩

/-- The (real) spectrum of the almost Mathieu operator is nonempty. -/
