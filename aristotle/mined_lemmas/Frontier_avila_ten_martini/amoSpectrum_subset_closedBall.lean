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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have h0 : ‖lp.single (E := fun _ : ℤ => ℂ) 2 (0 : ℤ) (1 : ℂ)‖ = 0 := by rw [h]; simp
  rw [lp.norm_single (by norm_num)] at h0
  simp at h0

/-! ## Shift operators -/


theorem amoSpectrum_subset_closedBall (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Metric.closedBall 0 ‖amo lam alpha theta‖ := by
  intro E hE
  have h : ‖(E : ℂ)‖ ≤ ‖amo lam alpha theta‖ := spectrum.norm_le_norm_of_mem hE
  simpa [Real.norm_eq_abs, Complex.norm_real] using h

