/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-! ## The pure ring algebra behind Kato's construction -/

/-- The algebraic heart of the adiabatic theorem.  In a ring, let `p` be an idempotent,
`k` an element annihilating `p` on both sides (think of `k = H - E` with `p` the spectral
projection of the eigenvalue `E`), `d` the derivative of `p` (so that `d = d*p + p*d`), and `b`
a two-sided inverse of `k + p`.  Then the explicitly constructed element
`b*(1-p)*d*p - p*d*(1-p)*b` has commutator with `k` equal to `d`. -/

lemma hasDerivAt_expectation {ε : ℝ} (A : ℝ → (𝓗 →L[ℂ] 𝓗)) (A' : 𝓗 →L[ℂ] 𝓗)
    (hHam_sa : ∀ s, IsSelfAdjoint (Ham s)) (psi : ℝ → 𝓗) (s : ℝ)
    (hpsi : HasDerivAt psi (-(Complex.I / ε) • (Ham s (psi s))) s)
    (hA : HasDerivAt A A' s) :
    HasDerivAt (fun t => ⟪psi t, A t (psi t)⟫_ℂ)
      (⟪psi s, A' (psi s)⟫_ℂ
        + (Complex.I / ε) * ⟪psi s, ((Ham s * A s - A s * Ham s) (psi s))⟫_ℂ) s := by
  have hR : HasDerivAt (fun t => (A t).restrictScalars ℝ) (A'.restrictScalars ℝ) s :=
    (ContinuousLinearMap.restrictScalarsL ℂ 𝓗 𝓗 ℝ ℝ).hasFDerivAt.comp_hasDerivAt s hA
  have h1 : HasDerivAt (fun t => A t (psi t))
      (A' (psi s) + A s (-(Complex.I / ε) • (Ham s (psi s)))) s := hR.clm_apply hpsi
  have h2 := hpsi.inner ℂ h1
  convert h2 using 1
  have hsaa : ∀ x y : 𝓗, ⟪Ham s x, y⟫_ℂ = ⟪x, Ham s y⟫_ℂ := by
    intro x y; rw [← ContinuousLinearMap.adjoint_inner_left, (hHam_sa s).adjoint_eq]
  simp only [inner_add_right, inner_smul_left, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, inner_sub_right, map_smul, inner_smul_right]
  rw [hsaa]
  simp [Complex.conj_I]
  ring

/-- Conservation of the norm along the Schrödinger flow. -/
