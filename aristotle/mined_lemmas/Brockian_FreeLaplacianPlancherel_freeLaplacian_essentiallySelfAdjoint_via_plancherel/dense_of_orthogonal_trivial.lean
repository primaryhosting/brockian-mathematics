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

open MeasureTheory Complex
open scoped Real ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-! ## Essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A densely defined symmetric operator `T` with domain `D` in a complex Hilbert space is
*essentially self-adjoint* when both deficiency spaces are trivial, i.e. when the ranges of
`T + i` and `T - i` are dense. -/

lemma dense_of_orthogonal_trivial [CompleteSpace H] {K : Submodule ℂ H}
    (h : ∀ z : H, (∀ x ∈ K, ⟪x, z⟫ = 0) → z = 0) : Dense (K : Set H) := by
  have hbot : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    exact h z fun x hx => (Submodule.mem_orthogonal K z).mp hz x hx
  have htop : K.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.2 hbot
  have hcl : closure (K : Set H) = Set.univ := by
    have := congrArg (fun S : Submodule ℂ H => (S : Set H)) htop
    simpa [Submodule.topologicalClosure_coe] using this
  exact dense_iff_closure_eq.2 hcl

