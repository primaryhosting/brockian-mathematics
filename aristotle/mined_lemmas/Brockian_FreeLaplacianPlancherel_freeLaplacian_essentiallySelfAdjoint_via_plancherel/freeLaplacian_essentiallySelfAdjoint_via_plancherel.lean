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

theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel :
    IsEssentiallySelfAdjointCore ((incl V).toLinearMap) ((freeLaplacian V).toLinearMap) where
  denseRange_domain := denseRange_incl
  symmetric := freeLaplacian_symmetric
  denseRange_add_I := denseRange_freeLaplacian_add_smul Complex.I (by simp)
  denseRange_sub_I := by
    have := denseRange_freeLaplacian_add_smul (V := V) (-Complex.I) (by simp)
    simpa [sub_eq_add_neg, neg_smul] using this

/-- Triviality of the deficiency subspaces in adjoint form: if an `L²` function `u` is a weak
eigenfunction of the adjoint of the free Laplacian with non-real eigenvalue `z`, then `u = 0`. -/
