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

/-- The Hilbert space `ℓ²(ℤ; ℂ)` on which the almost Mathieu operator acts. -/
abbrev Ell2 := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial Ell2 := by
  refine ⟨lp.single 2 0 1, 0, ?_⟩
  intro h
  have := congrArg (fun f : Ell2 => (f : ℤ → ℂ) 0) h
  simp at this


theorem amoPotential_bound (lam alpha theta : ℝ) (n : ℤ) :
    ‖amoPotential lam alpha theta n‖ ≤ 2 * |lam| := by
  rw [amoPotential, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 : |Real.cos (2 * Real.pi * (theta + n * alpha))| ≤ 1 := Real.abs_cos_le_one _
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  nlinarith [abs_nonneg lam, abs_nonneg (Real.cos (2 * Real.pi * (theta + n * alpha)))]

