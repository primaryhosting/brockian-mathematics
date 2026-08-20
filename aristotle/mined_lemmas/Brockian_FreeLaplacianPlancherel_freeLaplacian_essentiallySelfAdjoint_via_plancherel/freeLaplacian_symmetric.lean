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

lemma freeLaplacian_symmetric (f g : 𝓢(V, ℂ)) :
    inner ℂ (freeLaplacian V f) (incl V g) = inner ℂ (incl V f) (freeLaplacian V g) := by
  have key := SchwartzMap.integral_bilinear_laplacian_right_eq_left (μ := (volume : Measure V)) f g
    ((ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, ContinuousLinearMap.mul_apply'] at key
  simp only [freeLaplacian_apply, incl_apply, inner_neg_left, inner_neg_right,
    SchwartzMap.inner_toL2_toL2_eq, RCLike.inner_apply]
  have key2 : ∫ (x : V), g x * (starRingEnd ℂ) ((Δ f) x)
      = ∫ (x : V), (Δ g) x * (starRingEnd ℂ) (f x) := by
    calc ∫ (x : V), g x * (starRingEnd ℂ) ((Δ f) x)
        = ∫ (x : V), (starRingEnd ℂ) ((Δ f) x) * g x := by congr 1; funext x; ring
      _ = ∫ (x : V), (starRingEnd ℂ) (f x) * (Δ g) x := key.symm
      _ = _ := by congr 1; funext x; ring
  rw [key2]

/-- The operator `-Δ + c` is the composition of the inclusion with the Schwartz-space
operator `f ↦ -Δ f + c • f`. -/
