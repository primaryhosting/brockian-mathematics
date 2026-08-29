/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The `r`-neighbourhood of a set of sites `X` inside a metric space of sites. -/

theorem lieb_robinson_hypotheses_satisfiable :
    ∃ (loc : Set ℤ → Set (Quaternion ℝ)) (Z : ℕ → Set ℤ) (u v : ℕ → Quaternion ℝ),
      LocalStructure loc ∧ (∀ k, u k ∈ loc (Z k)) ∧ (∀ k, v k ∈ loc (Z k)) ∧
      (∀ k, u k * v k = 1) ∧ (∀ k, ‖u k‖ ≤ 1) ∧ (∀ k, ‖v k‖ ≤ 1) ∧
      (∀ k, ∀ z ∈ Z k, ∀ w ∈ Z k, dist z w ≤ 1) ∧
      (∃ x y : Quaternion ℝ, x ∈ loc {0} ∧ y ∈ loc {0} ∧ x * y ≠ y * x) := by
  refine ⟨demoLoc, fun _ => {0}, fun _ => 1, fun _ => 1, demoLoc_localStructure,
    fun _ => by simp [demoLoc], fun _ => by simp [demoLoc], fun _ => by simp,
    fun _ => by simp, fun _ => by simp, ?_, ?_⟩
  · intro k z hz w hw
    simp only [Set.mem_singleton_iff] at hz hw
    subst hz; subst hw
    simp
  · refine ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, by simp [demoLoc], by simp [demoLoc], ?_⟩
    simp [Quaternion.ext_iff]
    norm_num

end Frontier

