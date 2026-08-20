/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace
open Matrix

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

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The spread (standard deviation) of the observable `A` in the state `psi`:
the norm of `A psi` after subtracting its mean value `⟪psi, A psi⟫ • psi`. -/

lemma spread_sq_eq {A : H →ₗ[ℂ] H} (hA : IsSymmetricOp A) {psi : H} (hpsi : ‖psi‖ = 1) :
    (spread A psi) ^ 2 = (⟪psi, A (A psi)⟫_ℂ).re - ((⟪psi, A psi⟫_ℂ).re) ^ 2 := by
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  set a : ℂ := ⟪psi, A psi⟫_ℂ with ha_def
  have hac : (starRingEnd ℂ) a = a := conj_expectation hA psi
  have haim : a.im = 0 := by
    have := congrArg Complex.im hac
    rw [Complex.conj_im] at this
    linarith
  have hAp : ⟪A psi, psi⟫_ℂ = a := by rw [ha_def, hA]
  have hnorm : (spread A psi) ^ 2 = (⟪A psi - a • psi, A psi - a • psi⟫_ℂ).re := by
    rw [spread, ← ha_def, ← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
  rw [hnorm]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hself,
    hac, hAp, mul_one, ← hA psi (A psi)]
  simp only [Complex.sub_re, Complex.mul_re, haim, ← ha_def]
  ring

/-- **Heisenberg uncertainty principle** (absolute-value form).

For symmetric operators `X` and `P` on a complex inner product space and a normalized state
`psi` satisfying the canonical commutation relation `[X, P] psi = i·ℏ·psi`, the product of the
spreads of `X` and `P` in the state `psi` is at least `|ℏ|/2`. -/
