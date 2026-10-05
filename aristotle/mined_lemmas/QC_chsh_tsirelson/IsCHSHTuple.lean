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
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open scoped RealInnerProductSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In a unital C⋆-algebra, a self-adjoint element sandwiched between `-r` and `r`
(as multiples of the unit) has norm at most `r`. -/

theorem IsCHSHTuple.neg_B {a₀ a₁ b₀ b₁ : A} (T : IsCHSHTuple a₀ a₁ b₀ b₁) :
    IsCHSHTuple a₀ a₁ (-b₀) (-b₁) where
  A₀_inv := T.A₀_inv
  A₁_inv := T.A₁_inv
  B₀_inv := by simpa using T.B₀_inv
  B₁_inv := by simpa using T.B₁_inv
  A₀_sa := T.A₀_sa
  A₁_sa := T.A₁_sa
  B₀_sa := by simp [T.B₀_sa]
  B₁_sa := by simp [T.B₁_sa]
  A₀B₀_commutes := by simp [T.A₀B₀_commutes]
  A₀B₁_commutes := by simp [T.A₀B₁_commutes]
  A₁B₀_commutes := by simp [T.A₁B₀_commutes]
  A₁B₁_commutes := by simp [T.A₁B₁_commutes]

/-- The CHSH operator of a CHSH tuple is self-adjoint. -/
