import Mathlib

/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace Phys

/-- **Hellmann–Feynman theorem.**

Let `Ham : ℝ → V →L[ℂ] V` be a family of (self-adjoint) Hamiltonians on a complex Hilbert
space `V`, depending on a real parameter `l`, and let `psi l` be a normalized eigenvector of
`Ham l` with real eigenvalue `En l`.  If `Ham`, `psi` and `En` are differentiable at `l₀`,
with derivatives `dHam`, `dpsi` and `dEn`, then

`dE_n/dl = ⟪ψ_n, (∂H/∂l) ψ_n⟫`.

Only differentiability at `l₀`, self-adjointness of `Ham l₀`, and normalization of `psi l₀`
are needed (the eigenvalue equation is of course needed on a whole neighbourhood — here it is
assumed for all parameters). -/
theorem hellmann_feynman
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (Ham : ℝ → V →L[ℂ] V) (dHam : V →L[ℂ] V) (psi : ℝ → V) (dpsi : V)
    (En : ℝ → ℝ) (dEn : ℝ) (l₀ : ℝ)
    (hHam : HasDerivAt Ham dHam l₀)
    (hpsi : HasDerivAt psi dpsi l₀)
    (hEn : HasDerivAt En dEn l₀)
    (heig : ∀ l, Ham l (psi l) = (En l : ℂ) • psi l)
    (hnorm : ⟪psi l₀, psi l₀⟫_ℂ = 1)
    (hsa : IsSelfAdjoint (Ham l₀)) :
    (dEn : ℂ) = ⟪psi l₀, dHam (psi l₀)⟫_ℂ := by
  -- The derivative of `Ham`, viewed as a family of `ℝ`-linear maps.
  have hHamR : HasDerivAt (fun l => (Ham l).restrictScalars ℝ) (dHam.restrictScalars ℝ) l₀ :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp_hasDerivAt l₀ hHam
  -- Differentiate both sides of the eigenvalue equation.
  have hL : HasDerivAt (fun l => Ham l (psi l)) (dHam (psi l₀) + Ham l₀ dpsi) l₀ :=
    hHamR.clm_apply hpsi
  have hR : HasDerivAt (fun l => (En l : ℂ) • psi l)
      ((En l₀ : ℂ) • dpsi + (dEn : ℂ) • psi l₀) l₀ :=
    hEn.ofReal_comp.smul hpsi
  rw [funext heig] at hL
  have key : dHam (psi l₀) + Ham l₀ dpsi = (En l₀ : ℂ) • dpsi + (dEn : ℂ) • psi l₀ :=
    hL.unique hR
  -- Self-adjointness moves `Ham l₀` onto the eigenvector, where it acts by the real scalar `En l₀`.
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa (psi l₀) dpsi
  simp only [ContinuousLinearMap.coe_coe] at hsym
  have h1 : ⟪psi l₀, Ham l₀ dpsi⟫_ℂ = (En l₀ : ℂ) * ⟪psi l₀, dpsi⟫_ℂ := by
    rw [← hsym, heig l₀, inner_smul_left]
    simp
  -- Pair the differentiated eigenvalue equation with `psi l₀`; the `dpsi` terms cancel.
  have h2 := congrArg (fun v => ⟪psi l₀, v⟫_ℂ) key
  simp only [inner_add_right, inner_smul_right, h1, hnorm] at h2
  linear_combination -h2

end Phys

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

