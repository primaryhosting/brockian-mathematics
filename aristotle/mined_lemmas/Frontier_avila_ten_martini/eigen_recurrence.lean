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


lemma eigen_recurrence {lam alpha theta : ℝ} {E : ℂ} {u : H2}
    (hu : almostMathieu lam alpha theta u = E • u) (n : ℤ) :
    (u : ℤ → ℂ) (n + 1)
      = (E - (amPotential lam alpha theta n : ℂ)) * (u : ℤ → ℂ) n - (u : ℤ → ℂ) (n - 1) := by
  have h : (almostMathieu lam alpha theta u : ℤ → ℂ) n = ((E • u : H2) : ℤ → ℂ) n := by rw [hu]
  rw [almostMathieu_apply] at h
  have h2 : ((E • u : H2) : ℤ → ℂ) n = E * (u : ℤ → ℂ) n := rfl
  rw [h2] at h
  have hv : ((2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha)) : ℝ) : ℂ)
      = ((amPotential lam alpha theta n : ℝ) : ℂ) := rfl
  rw [hv] at h
  linear_combination h

/-- An eigenvector of the almost Mathieu operator is determined by its values at `0` and `1`. -/
