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

theorem eq_zero_of_dense_inner_eq_zero {s : Set H} (hs : Dense s) {y : H}
    (h : ∀ v ∈ s, ⟪y, v⟫ = 0) : y = 0 := by
  have hcont : Continuous fun w : H => ⟪y, w⟫ := (innerSL ℂ y).continuous
  have hall : ∀ w : H, ⟪y, w⟫ = 0 := by
    have : (fun w : H => ⟪y, w⟫) = fun _ : H => (0 : ℂ) :=
      hcont.ext_on hs continuous_const h
    exact fun w => congrFun this w
  simpa using hall y

/-- The adjoint is antitone. -/
