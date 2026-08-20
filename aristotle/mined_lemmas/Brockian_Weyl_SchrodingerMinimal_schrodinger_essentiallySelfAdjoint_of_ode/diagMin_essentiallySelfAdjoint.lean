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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate Real
open LinearPMap Submodule

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Essential self-adjointness -/

section Abstract

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A densely defined operator `A` is *essentially self-adjoint* when it is symmetric and its
adjoint is self-adjoint (equivalently, its closure is self-adjoint; equivalently, it has a
unique self-adjoint extension, see `unique_selfAdjoint_extension`). -/

theorem diagMin_essentiallySelfAdjoint : IsEssentiallySelfAdjoint (diagMin b lam) := by
  refine ⟨diagMin_dense b lam, diagMin_symmetric b lam, ?_⟩
  have hle := diagMin_le_adjoint b lam
  have hdense' : Dense (((diagMin b lam).adjoint).domain : Set E) :=
    (diagMin_dense b lam).mono fun x hx => hle.1 hx
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm (adjoint_le_adjoint_of_le (diagMin_dense b lam) hle)
    ((adjoint_symmetric b lam).le_adjoint hdense')

end Abstract

/-! ## The minimal Schrödinger operator on the circle -/

section Circle

open AddCircle MeasureTheory

variable (T : ℝ) [hT : Fact (0 < T)]

/-- The eigenvalue of the `n`-th Fourier mode for the Schrödinger operator `-d²/dx² + V₀`. -/
