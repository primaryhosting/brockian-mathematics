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
# The basic criterion for essential self-adjointness

This file develops the abstract operator-theoretic input for `Brockian.Weyl.FreeLaplacian2`:
a densely defined symmetric operator on a complex Hilbert space whose two deficiency ranges
`Ran (T + i)` and `Ran (T - i)` are dense has self-adjoint closure, i.e. it is
*essentially self-adjoint*.
-/

namespace Brockian.Weyl

open LinearPMap Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `x ↦ T x + z • x` on the domain of `T`. -/

theorem isFormalAdjoint_closure {T : H →ₗ.[ℂ] H} (hdom : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) : T.closure.IsFormalAdjoint T.closure := by
  intro x y
  have hle : T.closure ≤ (T.closure)† := by
    rw [adjoint_closure_eq hdom hsymm]; exact closure_le_adjoint hdom hsymm
  have hx : (x : H) ∈ (T.closure)†.domain := hle.1 x.2
  have hval : T.closure x = (T.closure)† ⟨(x : H), hx⟩ := hle.2 rfl
  rw [hval]
  exact LinearPMap.adjoint_isFormalAdjoint (dense_domain_closure hdom) ⟨(x : H), hx⟩ y

/-- If the deficiency range of `T` is dense, the corresponding deficiency range of the closure
is everything. -/
