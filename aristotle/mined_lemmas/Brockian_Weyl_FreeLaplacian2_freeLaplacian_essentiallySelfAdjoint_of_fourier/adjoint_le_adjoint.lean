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

theorem adjoint_le_adjoint {T S : H →ₗ.[ℂ] H} (hT : Dense (T.domain : Set H)) (h : T ≤ S) :
    S† ≤ T† := by
  have hS : Dense (S.domain : Set H) := Dense.mono (fun _ hx => h.1 hx) hT
  refine LinearPMap.IsFormalAdjoint.le_adjoint hT ?_
  intro x y
  have hx : (x : H) ∈ S.domain := h.1 x.2
  have hTx : T x = S ⟨(x : H), hx⟩ := h.2 rfl
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := S) hS y ⟨(x : H), hx⟩
  rw [hTx, ← inner_conj_symm, ← inner_conj_symm ((x : H))]
  simp only [hfa]

omit [CompleteSpace H] in
/-- For a symmetric operator `A` we have `‖x‖ ≤ ‖A x + i x‖`. -/
