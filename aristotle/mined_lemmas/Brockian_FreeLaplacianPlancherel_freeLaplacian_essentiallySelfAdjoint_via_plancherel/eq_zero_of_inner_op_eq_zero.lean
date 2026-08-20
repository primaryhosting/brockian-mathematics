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

lemma eq_zero_of_inner_op_eq_zero (c : ℂ) (hc : c.im ≠ 0) (u : Lp (α := V) ℂ 2)
    (hu : ∀ f : 𝓢(V, ℂ), inner ℂ (freeLaplacian V f + c • incl V f) u = 0) : u = 0 := by
  have hmain : ∀ f : 𝓢(V, ℂ),
      inner ℂ (incl V (𝓕 (-(Δ f) + c • f) : 𝓢(V, ℂ))) (𝓕 u : Lp (α := V) ℂ 2 volume) = 0 := by
    intro f
    rw [incl_fourier, Lp.inner_fourier_eq, ← op_eq_incl]
    exact hu f
  have hzero : ∀ g : V → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • ((𝓕 u : Lp (α := V) ℂ 2 volume) x) = 0 := by
    intro g hg hsupp
    obtain ⟨f, hf⟩ := exists_schwartz_fourier_eq c hc g hg hsupp
    have h2 := hmain f
    rw [L2.inner_def] at h2
    have hcoe := (𝓕 (-(Δ f) + c • f) : 𝓢(V, ℂ)).coeFn_toLp 2 (μ := (volume : Measure V))
    rw [← h2]
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [incl_apply, hx, RCLike.inner_apply, hf x]
    simp [Complex.real_smul, mul_comm]
  have hloc : LocallyIntegrable (fun x => (𝓕 u : Lp (α := V) ℂ 2 volume) x) (volume : Measure V) :=
    (Lp.memLp _).locallyIntegrable one_le_two
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hzero
  have hv0 : (𝓕 u : Lp (α := V) ℂ 2 volume) = 0 := Lp.eq_zero_iff_ae_eq_zero.2 hae
  have hu' : u = 𝓕⁻ (𝓕 u : Lp (α := V) ℂ 2 volume) := (FourierTransform.fourierInv_fourier_eq u).symm
  rw [hu', hv0]
  simp

/-- For any non-real complex number `c`, the operator `-Δ + c` has dense range. -/
