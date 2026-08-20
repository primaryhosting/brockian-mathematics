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

theorem freeLaplacian_isSymmetric : (freeLaplacian V).IsFormalAdjoint (freeLaplacian V) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨f, rfl⟩ := hx
  obtain ⟨g, rfl⟩ := hy
  rw [freeLaplacian_apply, freeLaplacian_apply, inner_toL2, inner_toL2]
  have hIBP : ∫ x, (starRingEnd ℂ) (f x) * (Δ g) x = ∫ x, (starRingEnd ℂ) ((Δ f) x) * g x :=
    SchwartzMap.integral_bilinear_laplacian_right_eq_left f g sesqMul
  have h1 : ∀ x : V, (starRingEnd ℂ) ((-(Δ f)) x) * g x
      = -((starRingEnd ℂ) ((Δ f) x) * g x) := by
    intro x; simp
  have h2 : ∀ x : V, (starRingEnd ℂ) (f x) * ((-(Δ g)) x)
      = -((starRingEnd ℂ) (f x) * (Δ g) x) := by
    intro x; simp
  simp only [h1, h2, integral_neg, hIBP]

/-! ### Density of the deficiency ranges -/

