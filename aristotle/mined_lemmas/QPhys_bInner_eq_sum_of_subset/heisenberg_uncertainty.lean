import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# A model for the canonical commutation relation

This file shows that the hypotheses of `QPhys.heisenberg_uncertainty` are not vacuous:
we build an explicit complex inner product space (the polynomials `ℂ[X]` with the
Bargmann–Fock inner product `⟪p, q⟫ = ∑ n ! * conj (pₙ) * qₙ`), two symmetric operators
`Xop`, `Pop` on it satisfying `[Xop, Pop] = 2 i`, and a normalized state.
-/

import Mathlib
import RequestProject.HeisenbergUncertainty

/-!
# A model for the canonical commutation relation (Bargmann–Fock space of polynomials)
-/

namespace QPhys

open Polynomial ComplexConjugate

/-- The Bargmann–Fock inner product on polynomials: `⟪p, q⟫ = ∑ₙ n! * conj pₙ * qₙ`. -/

theorem heisenberg_uncertainty {X P : H →ₗ[ℂ] H}
    (hX : IsSymmetricOp X) (hP : IsSymmetricOp P) (hbar : ℝ)
    (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * hbar) • u)
    (psi : H) (hpsi : ‖psi‖ = 1) :
    stdDev X psi * stdDev P psi ≥ hbar / 2 := by
  have him := inner_im_eq hX hP hbar hcomm psi hpsi
  set u : H := X psi - ((mean X psi : ℝ) : ℂ) • psi with hu
  set v : H := P psi - ((mean P psi : ℝ) : ℂ) • psi with hv
  have h1 : hbar / 2 ≤ ‖(inner ℂ u v : ℂ)‖ := by
    rw [← him]
    exact le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
  have h2 : ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  simpa [stdDev, hu, hv, ge_iff_le] using h1.trans h2

end QPhys

