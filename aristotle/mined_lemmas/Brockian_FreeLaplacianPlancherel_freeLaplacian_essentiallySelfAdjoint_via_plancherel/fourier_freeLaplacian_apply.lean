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

open MeasureTheory SchwartzMap Real FourierTransform ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-! ### An abstract criterion for essential self-adjointness

We use the classical *basic criterion* (von Neumann's deficiency criterion): a densely defined
symmetric operator `T` on a Hilbert space is essentially self-adjoint if and only if the ranges of
`T + i` and `T - i` are dense.  Here the operator is given on a core `D` (an abstract vector space,
mapped into the Hilbert space by `ι`, e.g. the Schwartz space sitting inside `L²`). -/

/-- `IsEssentiallySelfAdjointCore ι T` states that the operator `T`, acting on the core `D` which is
embedded into the Hilbert space `H` via `ι`, is a densely defined symmetric operator whose
deficiency spaces are trivial, i.e. the ranges of `T ± i` are dense.  By von Neumann's basic
criterion this is exactly essential self-adjointness of `T` on the core `ι '' D`. -/
structure IsEssentiallySelfAdjointCore {D H : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : D →ₗ[ℂ] H) (T : D →ₗ[ℂ] D) : Prop where
  /-- the core is dense in the Hilbert space -/
  dense_domain : Dense (Set.range ι)
  /-- the operator is symmetric on the core -/
  symmetric : ∀ f g : D, inner ℂ (ι (T f)) (ι g) = inner ℂ (ι f) (ι (T g))
  /-- the range of `T + i` is dense -/
  dense_range_add_I : Dense (Set.range fun f : D => ι (T f) + Complex.I • ι f)
  /-- the range of `T - i` is dense -/
  dense_range_sub_I : Dense (Set.range fun f : D => ι (T f) - Complex.I • ι f)

/-! ### The free Laplacian on the Schwartz space -/

/-- The free Laplacian `-d²/dx²` acting on the Schwartz space `𝓢(ℝ, ℂ)`. -/

theorem fourier_freeLaplacian_apply (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (freeLaplacian f) : 𝓢(ℝ, ℂ)) ξ = (lapMultiplier ξ : ℂ) * (𝓕 f : 𝓢(ℝ, ℂ)) ξ := by
  have h1 : freeLaplacian f = -(derivCLM ℂ ℂ (derivCLM ℂ ℂ f)) := by
    ext x; simp [freeLaplacian]
  have h2 : (𝓕 (freeLaplacian f) : 𝓢(ℝ, ℂ)) = -(𝓕 (derivCLM ℂ ℂ (derivCLM ℂ ℂ f))) := by
    rw [h1, ← SchwartzMap.fourierTransformCLM_apply ℂ, map_neg,
      SchwartzMap.fourierTransformCLM_apply]
  rw [h2, SchwartzMap.neg_apply, fourier_derivCLM_apply, fourier_derivCLM_apply]
  have h3 : (2 * (π : ℂ) * Complex.I * ξ) * (2 * (π : ℂ) * Complex.I * ξ)
      = -((lapMultiplier ξ : ℝ) : ℂ) := by
    simp only [lapMultiplier]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← mul_assoc, h3]
  ring

/-- The free Laplacian is a symmetric operator on the Schwartz space, as one sees on the Fourier
side, where it becomes multiplication by the real function `4π²ξ²`. -/
