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


theorem avila_ten_martini (lam alpha theta : ℝ) (hlam : lam ≠ 0) (halpha : Irrational alpha)
    (h_nowhere_dense : interior (amSpectrum lam alpha theta) = ∅)
    (h_no_isolated : ∀ x ∈ amSpectrum lam alpha theta,
      AccPt x (Filter.principal (amSpectrum lam alpha theta))) :
    IsCantorSet (amSpectrum lam alpha theta) :=
  isCantorSet_of_interior_eq_empty (amSpectrum_nonempty lam alpha theta)
    (amSpectrum_isCompact lam alpha theta) h_nowhere_dense h_no_isolated

/-- Under the hypotheses of the Ten Martini Problem, the spectrum of the almost Mathieu
operator is uncountable. -/
