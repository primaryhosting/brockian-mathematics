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


lemma abs_amPotential_le (lam alpha theta : ℝ) (n : ℤ) :
    |amPotential lam alpha theta n| ≤ 2 * |lam| := by
  have h := Real.abs_cos_le_one (2 * Real.pi * (theta + n * alpha))
  have h2 : |2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha))|
      = 2 * |lam| * |Real.cos (2 * Real.pi * (theta + n * alpha))| := by
    rw [abs_mul, abs_mul]
    norm_num
  rw [amPotential, h2]
  nlinarith [abs_nonneg lam, abs_nonneg (Real.cos (2 * Real.pi * (theta + n * alpha)))]

/-- The **almost Mathieu operator** `H_{lam, alpha, theta}` on `ℓ²(ℤ, ℂ)`:
`(H u) n = u (n + 1) + u (n - 1) + 2 * lam * cos (2 * π * (theta + n * alpha)) * u n`. -/
