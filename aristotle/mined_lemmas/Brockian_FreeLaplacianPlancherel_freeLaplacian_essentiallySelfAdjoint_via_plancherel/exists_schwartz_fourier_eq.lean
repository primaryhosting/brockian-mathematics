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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap FourierTransform Laplacian LineDeriv
open scoped ContDiff

namespace Brockian.FreeLaplacianPlancherel

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Von Neumann's basic criterion for essential self-adjointness of a symmetric operator
`A` defined on a dense domain, presented abstractly: the domain is a complex vector space `D`
mapped into the Hilbert space `H` by `ι` with dense range, `A` is symmetric, and the operators
`A ± i` have dense range (i.e. both deficiency subspaces are trivial). -/
structure IsEssentiallySelfAdjointCore {D H : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι A : D →ₗ[ℂ] H) : Prop where
  /-- The operator is densely defined. -/
  denseRange_domain : DenseRange ι
  /-- The operator is symmetric on its domain. -/
  symmetric : ∀ f g : D, inner ℂ (A f) (ι g) = inner ℂ (ι f) (A g)
  /-- The deficiency subspace at `i` is trivial. -/
  denseRange_add_I : DenseRange fun f : D => A f + Complex.I • ι f
  /-- The deficiency subspace at `-i` is trivial. -/
  denseRange_sub_I : DenseRange fun f : D => A f - Complex.I • ι f

variable (V) in
/-- The inclusion of the Schwartz space into `L²`, i.e. the domain of the free Laplacian. -/

lemma exists_schwartz_fourier_eq (c : ℂ) (hc : c.im ≠ 0) (g : V → ℝ) (hg : ContDiff ℝ ∞ g)
    (hsupp : HasCompactSupport g) :
    ∃ f : 𝓢(V, ℂ), ∀ ξ, 𝓕 (-(Δ f) + c • f : 𝓢(V, ℂ)) ξ = (g ξ : ℂ) := by
  have hne : ∀ ξ : V, ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c ≠ 0 := by
    intro ξ h
    apply hc
    have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.zero_im, zero_add] at h2
    exact h2
  have hden : ContDiff ℝ ∞ (fun ξ : V => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c) := by
    have h1 : ContDiff ℝ ∞ (fun ξ : V => (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) := by
      have : ContDiff ℝ ∞ (fun ξ : V => ‖ξ‖ ^ 2) := contDiff_norm_sq ℝ
      fun_prop
    exact (Complex.ofRealCLM.contDiff.comp h1).add contDiff_const
  have hnum : ContDiff ℝ ∞ (fun ξ : V => (g ξ : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hsmooth : ContDiff ℝ ∞
      (fun ξ : V => (g ξ : ℂ) * (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c)⁻¹) :=
    hnum.mul (hden.inv hne)
  have hcs : HasCompactSupport
      (fun ξ : V => (g ξ : ℂ) * (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c)⁻¹) := by
    have : HasCompactSupport (fun ξ : V => (g ξ : ℂ)) :=
      hsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    exact this.mul_right
  refine ⟨𝓕⁻ (hcs.toSchwartzMap hsmooth), fun ξ => ?_⟩
  rw [fourier_op_apply, FourierTransform.fourier_fourierInv_eq]
  show (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c) *
      ((g ξ : ℂ) * (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c)⁻¹) = (g ξ : ℂ)
  rw [mul_comm (g ξ : ℂ), ← mul_assoc, mul_inv_cancel₀ (hne ξ), one_mul]

/-- If an `L²` function is orthogonal to the range of `-Δ + c` (`c` non-real), it vanishes.
This is the triviality of the deficiency subspaces, obtained from Plancherel's theorem. -/
