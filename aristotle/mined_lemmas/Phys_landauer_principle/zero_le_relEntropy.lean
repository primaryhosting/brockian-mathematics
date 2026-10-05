import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-! ## Shannon entropy -/

/-- Shannon entropy (in nats) of a finitely supported weight function. -/

lemma zero_le_relEntropy {α : Type*} [Fintype α] (f g : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hsupp : ∀ x, g x = 0 → f x = 0)
    (hsum : ∑ x : α, g x ≤ ∑ x : α, f x) :
    0 ≤ (∑ x : α, f x * Real.log (f x)) - ∑ x : α, f x * Real.log (g x) := by
  have key : ∑ x : α, (f x - g x) ≤
      ∑ x : α, (f x * Real.log (f x) - f x * Real.log (g x)) :=
    Finset.sum_le_sum fun x _ =>
      sub_le_mul_log_sub_mul_log (f x) (g x) (hf x) (hg x) (hsupp x)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at key
  linarith

/-! ## Gibbs states -/

variable {M B : Type*} [Fintype M] [Fintype B]

/-- The canonical (Gibbs) distribution of a bath with energy levels `E`
at inverse temperature `beta`. -/
