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

/-
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform InnerProductSpace Laplacian

noncomputable section

/-- A densely defined operator `A` on a Hilbert space is *essentially self-adjoint* if its
adjoint is self-adjoint (equivalently, if the closure `A** = A*` of `A` is self-adjoint). -/

theorem freeLaplacian_essentiallySelfAdjoint_of_fourier :
    IsEssentiallySelfAdjoint (freeLaplacian V) := by
  refine ⟨dense_domain_freeLaplacian V, ?_⟩
  have hdense := dense_domain_freeLaplacian V
  have hle : freeLaplacian V ≤ (freeLaplacian V).adjoint :=
    (freeLaplacian_isFormalAdjoint_self V).le_adjoint hdense
  have hdense' : Dense (((freeLaplacian V).adjoint.domain : Submodule ℂ (L2Space V)) :
      Set (L2Space V)) :=
    hdense.mono (fun _ hx => hle.1 hx)
  have h1 : (freeLaplacian V).adjoint ≤ (freeLaplacian V).adjoint.adjoint :=
    (adjoint_isFormalAdjoint_self V).le_adjoint hdense'
  have h2 : (freeLaplacian V).adjoint.adjoint ≤ (freeLaplacian V).adjoint :=
    adjoint_antitone hdense' hdense hle
  exact LinearPMap.isSelfAdjoint_def.2 (le_antisymm h2 h1)

/-- The free Laplacian on `L²(ℝ^d, ℂ)` is essentially self-adjoint on the Schwartz space. -/
