/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A *time-reversal operator* on a complex inner product space: an antiunitary map `T`
(additive, conjugate-homogeneous, and inner-product reversing) which squares to `-1`.
The condition `T (T a) = -a` is exactly what holds for half-integer spin
(for integer spin one has `T² = +1`). -/
structure IsTimeReversal (T : V → V) : Prop where
  /-- `T` is additive. -/
  map_add : ∀ a b, T (a + b) = T a + T b
  /-- `T` is conjugate-homogeneous. -/
  map_smul : ∀ (c : ℂ) (a : V), T (c • a) = (starRingEnd ℂ) c • T a
  /-- `T` is antiunitary: it conjugates inner products. -/
  inner_map : ∀ a b, ⟪T a, T b⟫_ℂ = ⟪b, a⟫_ℂ
  /-- Half-integer spin: `T² = -1`. -/
  sq_eq_neg : ∀ a, T (T a) = -a

/-- For a half-integer-spin time reversal, `T x` is orthogonal to `x`. -/

noncomputable def spinHalfT : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) :=
  fun x => WithLp.toLp 2 ![-(starRingEnd ℂ) (x 1), (starRingEnd ℂ) (x 0)]

