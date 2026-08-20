/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

noncomputable section

/-- The standard symplectic vector space `ℝ^{2n} ≃ ℂ^n`, equipped with its Euclidean
structure.  The standard symplectic form is the imaginary part of the Hermitian inner
product. -/
abbrev SymplecticSpace (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The standard symplectic form on `ℂ^n ≃ ℝ^{2n}`:
`ω(z, w) = Im ⟪z, w⟫ = ∑ i, (x i * v i - y i * u i)`, where `z i = x i + I * y i` and
`w i = u i + I * v i`. -/

lemma norm_le_of_inner_bound {n : ℕ} {c : SymplecticSpace n} {r R : ℝ}
    (hR : 0 ≤ R) (h : ∀ v : SymplecticSpace n, ‖v‖ < r → ⟪c, v⟫_ℝ < R) :
    r * ‖c‖ ≤ R := by
  by_contra hcon
  push_neg at hcon
  have hc : 0 < ‖c‖ := by
    rcases (norm_nonneg c).lt_or_eq with h1 | h1
    · exact h1
    · exfalso; rw [← h1] at hcon; simp at hcon; linarith
  set t : ℝ := (R / ‖c‖ + r) / 2 with ht
  have h1 : R / ‖c‖ < r := by rw [div_lt_iff₀ hc]; linarith
  have h2 : R / ‖c‖ < t := by rw [ht]; linarith
  have h3 : t < r := by rw [ht]; linarith
  have h4 : 0 < t := lt_of_le_of_lt (div_nonneg hR hc.le) h2
  have hv : ‖(t / ‖c‖) • c‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos h4 hc)]
    field_simp
  have hlt := h ((t / ‖c‖) • c) (by rw [hv]; exact h3)
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at hlt
  have h5 : t * ‖c‖ < R := by
    calc t * ‖c‖ = t / ‖c‖ * ‖c‖ ^ 2 := by field_simp
      _ < R := hlt
  rw [div_lt_iff₀ hc] at h2
  linarith

/-- The analytic core of the nonsqueezing statement: if a linear symplectic map sends every
vector of norm `< r` to a vector whose first complex coordinate has modulus `< R`, then
`r ≤ R`. -/
