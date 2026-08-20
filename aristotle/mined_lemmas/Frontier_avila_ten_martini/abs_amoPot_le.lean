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


theorem abs_amoPot_le (lam alpha theta : ℝ) (n : ℤ) : |amoPot lam alpha theta n| ≤ 2 * |lam| := by
  have h := Real.abs_cos_le_one (2 * π * (theta + n * alpha))
  calc |amoPot lam alpha theta n| = (2 * |lam|) * |Real.cos (2 * π * (theta + n * alpha))| := by
        rw [amoPot, abs_mul, abs_mul]
        simp
    _ ≤ (2 * |lam|) * 1 := by
        have : (0 : ℝ) ≤ 2 * |lam| := by positivity
        exact mul_le_mul_of_nonneg_left h this
    _ = 2 * |lam| := by ring

/-- The almost Mathieu operator with coupling `lam`, flux `alpha` and phase `theta`:
`(H u) n = u (n + 1) + u (n - 1) + 2 * lam * cos (2 * π * (theta + n * alpha)) * u n`. -/
