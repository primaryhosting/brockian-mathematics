/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace QPhys

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

theorem half_le_norm_mul_norm_of_inner_sub_inner (u v : H) (c : ℝ)
    (h : inner ℂ u v - inner ℂ v u = (c : ℂ) * Complex.I) :
    c / 2 ≤ ‖u‖ * ‖v‖ := by
  have hconj : (starRingEnd ℂ) (inner ℂ u v) = inner ℂ v u := inner_conj_symm v u
  have hsub : (inner ℂ u v : ℂ) - (starRingEnd ℂ) (inner ℂ u v)
      = ((2 * (inner ℂ u v : ℂ).im : ℝ) : ℂ) * Complex.I := Complex.sub_conj _
  rw [hconj] at hsub
  rw [h] at hsub
  have him : c = 2 * (inner ℂ u v : ℂ).im := by
    have := mul_right_cancel₀ Complex.I_ne_zero hsub
    exact_mod_cast this
  have h1 : (inner ℂ u v : ℂ).im ≤ ‖(inner ℂ u v : ℂ)‖ :=
    le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
  have h2 : ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have := h1.trans h2
  rw [him]
  linarith

/-- **Heisenberg uncertainty relation** (Robertson form for the canonical commutator).
If `X` and `P` are symmetric operators on a complex inner product space, `ψ` is a
normalized state, and the expectation of the canonical commutator `[X,P]` in the state
`ψ` equals `i ℏ`, then the product of the uncertainties of `X` and `P` in the state `ψ`
is at least `ℏ/2`. -/
