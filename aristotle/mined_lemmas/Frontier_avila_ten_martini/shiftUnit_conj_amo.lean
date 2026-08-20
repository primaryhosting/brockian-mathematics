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


theorem shiftUnit_conj_amo (lam alpha theta : ℝ) :
    (shiftUnit : Ell2 →L[ℂ] Ell2) * amo lam alpha theta
        * ((shiftUnit⁻¹ : (Ell2 →L[ℂ] Ell2)ˣ) : Ell2 →L[ℂ] Ell2)
      = amo lam alpha (theta + alpha) := by
  ext f i
  show ((reindexCLM (Equiv.addRight (1 : ℤ)))
      ((amo lam alpha theta) ((reindexCLM (Equiv.addRight (-1 : ℤ))) f)) : ℤ → ℂ) i = _
  rw [reindexCLM_apply, amo_apply, amo_apply]
  simp only [reindexCLM_apply, Equiv.coe_addRight]
  have h1 : i + 1 + 1 + -1 = i + 1 := by ring
  have h2 : i + 1 - 1 + -1 = i - 1 := by ring
  have h3 : i + 1 + -1 = i := by ring
  have h4 : 2 * Real.pi * (theta + ((i + 1 : ℤ) : ℝ) * alpha)
      = 2 * Real.pi * (theta + alpha + (i : ℝ) * alpha) := by push_cast; ring
  rw [h1, h2, h3, h4]

/-! ## The spectrum of the almost Mathieu operator -/

/-- The spectrum of the almost Mathieu operator, viewed as a subset of `ℝ`
(legitimate since the operator is self-adjoint). -/
