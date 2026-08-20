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

set_option grind.warning false

namespace QC

variable {A : Type*}

/-- The CHSH operator associated to a tuple of observables
`A₀, A₁` (Alice) and `B₀, B₁` (Bob). -/

theorem isSelfAdjoint_chshOp (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    IsSelfAdjoint (chshOp A₀ A₁ B₀ B₁) := by
  unfold IsSelfAdjoint chshOp
  simp only [star_sub, star_add, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
    ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]

end Ring

section CStar

variable [NormedRing A] [StarRing A] [CStarRing A] [NormOneClass A] {A₀ A₁ B₀ B₁ : A}

/-- A self-adjoint involution in a C⋆-algebra has norm one. -/
