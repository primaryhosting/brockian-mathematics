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

lemma fourier_laplacian_apply (f : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (Δ f) ξ = (-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) : ℝ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ V with hb
  have h1 : ∀ (m : V) (h : 𝓢(V, ℂ)) (ζ : V),
      𝓕 (∂_{m} h) ζ = (2 * Real.pi * Complex.I) * ((inner ℝ ζ m : ℝ) : ℂ) * 𝓕 h ζ := by
    intro m h ζ
    have ht : (fun x : V => (inner ℝ x m : ℝ)).HasTemperateGrowth := by fun_prop
    rw [SchwartzMap.fourier_lineDerivOp_eq h m]
    simp [ht, mul_assoc]
  have h2 : 𝓕 (Δ f) ξ = ∑ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ := by
    rw [SchwartzMap.laplacian_eq_sum b f, ← SchwartzMap.fourierTransformCLM_apply ℂ, map_sum]
    simp [SchwartzMap.sum_apply]
  have h3 : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ
      = -(4 * (Real.pi : ℂ) ^ 2 * ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2) * 𝓕 f ξ := by
    intro i
    rw [h1, h1]
    ring_nf
    simp [Complex.I_sq]
  have hsum : ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := b.sum_sq_inner_left ξ
  have h := congrArg (fun r : ℝ => (r : ℂ)) hsum
  push_cast at h
  rw [h2]
  simp only [h3, ← Finset.sum_mul]
  push_cast
  rw [← h, Finset.mul_sum]
  simp

/-- The free Laplacian is symmetric on the Schwartz space. -/
