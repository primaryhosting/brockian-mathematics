/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ, ℂ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev H2 := ℓ²(ℤ, ℂ)

instance : Nontrivial H2 := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have : (lp.single 2 (0 : ℤ) (1 : ℂ) : ℤ → ℂ) 0 = (0 : H2) 0 := by rw [h]
  simp [lp.single_apply] at this

/-! ## Shift operators -/


theorem amSpectrum_subset_Icc (lam alpha theta : ℝ) :
    amSpectrum lam alpha theta ⊆ Set.Icc (-(2 + 2 * |lam|)) (2 + 2 * |lam|) := by
  intro x hx
  have h : ‖x‖ ≤ ‖almostMathieu lam alpha theta‖ := spectrum.norm_le_norm_of_mem hx
  have h2 := norm_almostMathieu_le lam alpha theta
  rw [Real.norm_eq_abs] at h
  have := abs_le.mp (le_trans h h2)
  exact ⟨this.1, this.2⟩

/-! ## Cantor sets -/

/-- A subset of `ℝ` is a *Cantor set* if it is nonempty, compact, perfect (closed with no
isolated points) and totally disconnected. -/
