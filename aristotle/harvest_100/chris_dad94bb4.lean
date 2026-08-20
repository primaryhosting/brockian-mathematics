/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Heisenberg uncertainty principle.**

Let `X` and `P` be symmetric (formally self-adjoint) linear operators on a complex inner
product space `E` satisfying the canonical commutation relation `X P - P X = i ħ`, and let
`psi` be a normalized state.  Writing

* `Δx = ‖X psi - ⟪psi, X psi⟫ • psi‖`,
* `Δp = ‖P psi - ⟪psi, P psi⟫ • psi‖`

for the standard deviations of position and momentum in the state `psi` (here `⟪·,·⟫` is the
complex inner product, conjugate-linear in the first argument, so `⟪psi, X psi⟫` is the
expectation value of `X`), we have `Δx · Δp ≥ ħ / 2`.

The proof is the classical one: the expectation values `⟪psi, X psi⟫` and `⟪psi, P psi⟫` are
real by symmetry, the commutator forces the imaginary part of the inner product of the two
centred vectors to equal `ħ / 2`, and Cauchy–Schwarz bounds that inner product by the product
of the norms.

No positivity assumption on `ħ` is needed (for `ħ ≤ 0` the inequality is only weaker). -/
theorem heisenberg_uncertainty
    (X P : E →ₗ[ℂ] E) (hbar : ℝ)
    (hX : ∀ u v : E, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : E, inner ℂ (P u) v = inner ℂ u (P v))
    (hcomm : ∀ u : E, X (P u) - P (X u) = ((hbar : ℂ) * Complex.I) • u)
    (psi : E) (hpsi : ‖psi‖ = 1) :
    hbar / 2 ≤ ‖X psi - (inner ℂ psi (X psi) : ℂ) • psi‖ *
      ‖P psi - (inner ℂ psi (P psi) : ℂ) • psi‖ := by
  set a : ℂ := inner ℂ psi (X psi) with ha
  set b : ℂ := inner ℂ psi (P psi) with hb
  set u : E := X psi - a • psi with hu
  set v : E := P psi - b • psi with hv
  -- the state is normalized
  have hnn : inner ℂ psi psi = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  -- the expectation values are real
  have haa : (starRingEnd ℂ) a = a := by rw [ha, inner_conj_symm, hX]
  have hbb : (starRingEnd ℂ) b = b := by rw [hb, inner_conj_symm, hP]
  -- the canonical commutation relation, in inner product form
  have h1 : inner ℂ (X psi) (P psi) - inner ℂ (P psi) (X psi) = (hbar : ℂ) * I := by
    rw [hX psi (P psi), hP psi (X psi), ← inner_sub_right, hcomm psi, inner_smul_right, hnn,
      mul_one]
  have hxp : inner ℂ (X psi) psi = a := hX psi psi
  have hpp : inner ℂ (P psi) psi = b := hP psi psi
  -- the same relation for the centred vectors
  have hkey : inner ℂ u v - inner ℂ v u = (hbar : ℂ) * I := by
    rw [hu, hv]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, haa, hbb,
      hxp, hpp, hnn]
    linear_combination h1
  have h2 : (inner ℂ v u : ℂ).im = -(inner ℂ u v : ℂ).im := by
    have hconj : (inner ℂ v u : ℂ) = (starRingEnd ℂ) (inner ℂ u v) := (inner_conj_symm _ _).symm
    rw [hconj, Complex.conj_im]
  have him : (inner ℂ u v : ℂ).im = hbar / 2 := by
    have h3 := congrArg Complex.im hkey
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im] at h3
    rw [h2] at h3
    linarith
  calc hbar / 2 = (inner ℂ u v : ℂ).im := him.symm
    _ ≤ |(inner ℂ u v : ℂ).im| := le_abs_self _
    _ ≤ ‖(inner ℂ u v : ℂ)‖ := Complex.abs_im_le_norm _
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm _ _

end QPhys

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

