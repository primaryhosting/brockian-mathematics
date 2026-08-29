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
# A basic criterion for essential self-adjointness

Let `T` be a densely defined symmetric operator on a complex Hilbert space `H`.
If the ranges of `T + i` and `T - i` are both dense, then the adjoint `T†` is
self-adjoint, i.e. `T` is essentially self-adjoint.

Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open LinearPMap MeasureTheory Filter Topology

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The range of `T + z` for a partially defined operator `T` and a scalar `z`. -/

theorem hasTemperateGrowth_of_bounded_iteratedDeriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} (hf : ContDiff ℝ ∞ f)
    (h : ∀ n : ℕ, ∃ C : ℝ, ∀ t : ℝ, ‖iteratedDeriv n f t‖ ≤ C) :
    Function.HasTemperateGrowth f := by
  refine ⟨hf, fun n => ?_⟩
  obtain ⟨C, hC⟩ := h n
  refine ⟨0, C, fun t => ?_⟩
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hC t

/-- The iterated derivatives of `t ↦ (t + z)⁻¹` on the real line. -/
