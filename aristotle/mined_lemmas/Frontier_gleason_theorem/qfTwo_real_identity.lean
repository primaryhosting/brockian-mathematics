import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
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

namespace Frontier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A *frame function of weight one*, Gleason's formulation of a quantum measure:
a function on the unit sphere which is nonnegative and whose values sum to `1`
over every orthonormal basis. -/
structure IsFrameFunction (f : H → ℝ) : Prop where
  nonneg : ∀ x : H, ‖x‖ = 1 → 0 ≤ f x
  sum_eq_one : ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H, ∑ i, f (b i) = 1

/-- A density operator: a positive (hence self-adjoint) operator of trace one. -/

theorem qfTwo_real_identity (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1) (h3 : a * c = b * d) :
    a ^ 4 / (a ^ 4 + b ^ 4) + c ^ 4 / (c ^ 4 + d ^ 4) = 1 := by
  have hcb : c = b := by
    nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c)]
  have hda : d = a := by
    nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c)]
  have hpos : 0 < a ^ 4 + b ^ 4 := by nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  rw [hcb, hda, show b ^ 4 + a ^ 4 = a ^ 4 + b ^ 4 by ring, ← add_div, div_self hpos.ne']

/-- `qfTwo` adds up to one on any orthonormal pair. -/
