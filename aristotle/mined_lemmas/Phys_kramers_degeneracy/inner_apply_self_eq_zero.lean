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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- A *time-reversal operator* on a complex inner product space `V` for a system of
half-integer spin: an antiunitary map (additive, conjugate-linear, and antipreserving the
inner product) whose square is `-1`. -/
structure TimeReversal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- the underlying map -/
  toFun : V → V
  /-- additivity -/
  map_add : ∀ x y : V, toFun (x + y) = toFun x + toFun y
  /-- conjugate-linearity -/
  map_smul : ∀ (c : ℂ) (x : V), toFun (c • x) = (starRingEnd ℂ) c • toFun x
  /-- antiunitarity: `⟪T x, T y⟫ = ⟪y, x⟫` -/
  inner_map : ∀ x y : V, ⟪toFun x, toFun y⟫_ℂ = ⟪y, x⟫_ℂ
  /-- half-integer spin: `T² = -1` -/
  sq_eq_neg : ∀ x : V, toFun (toFun x) = -x

namespace TimeReversal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

instance : CoeFun (TimeReversal V) (fun _ => V → V) := ⟨TimeReversal.toFun⟩


theorem inner_apply_self_eq_zero (T : TimeReversal V) (x : V) : ⟪T x, x⟫_ℂ = 0 := by
  have h := T.inner_map x (T x)
  rw [T.sq_eq_neg x, inner_neg_right] at h
  linear_combination (-1 / 2 : ℂ) * h

