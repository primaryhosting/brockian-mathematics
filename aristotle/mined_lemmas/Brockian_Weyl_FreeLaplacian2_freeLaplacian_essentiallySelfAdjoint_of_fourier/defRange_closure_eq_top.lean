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

theorem defRange_closure_eq_top {T : H →ₗ.[ℂ] H} (hdom : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) {z : ℂ} (hz : z.re = 0) (hz1 : ‖z‖ = 1)
    (hdense : Dense (defRange T z : Set H)) : defRange T.closure z = ⊤ := by
  have hcl : T.IsClosable := isClosable_of_isFormalAdjoint_self hdom hsymm
  have hsub : (defRange T z : Set H) ⊆ (defRange T.closure z : Set H) := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨(x : H), T.le_closure.1 x.2⟩, by rw [defOp_apply, defOp_apply, ← T.le_closure.2 rfl]⟩
  have hdense' : Dense (defRange T.closure z : Set H) := hdense.mono hsub
  have hclosed : IsClosed (defRange T.closure z : Set H) :=
    isClosed_defRange hcl.closure_isClosed (isFormalAdjoint_closure hdom hsymm) hz hz1
  have : (defRange T.closure z : Set H) = Set.univ := by
    rw [← hclosed.closure_eq, hdense'.closure_eq]
  exact SetLike.coe_injective (by simpa using this)

/-- **The basic criterion for essential self-adjointness**: a densely defined symmetric
operator whose two deficiency ranges are dense has self-adjoint closure. -/
