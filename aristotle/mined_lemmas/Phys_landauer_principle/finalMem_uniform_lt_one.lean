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

theorem finalMem_uniform_lt_one [Nonempty B] (beta : ℝ) (E : B → ℝ)
    (U : Bool × B ≃ Bool × B) (m₀ : Bool) :
    finalMem beta E (fun _ => (1 / 2 : ℝ)) U m₀ < 1 := by
  have hp1 : ∑ _m : Bool, (1 / 2 : ℝ) = 1 := by
    rw [Fintype.sum_bool]; norm_num
  have hsum := finalMem_sum beta E (fun _ => (1 / 2 : ℝ)) hp1 U
  rw [Fintype.sum_bool] at hsum
  have hpos : ∀ m : Bool, 0 < finalMem beta E (fun _ => (1 / 2 : ℝ)) U m := by
    intro m
    refine Finset.sum_pos (fun b _ => ?_) (by simp [Finset.univ_nonempty])
    unfold finalJoint initJoint
    exact mul_pos (by norm_num) (gibbs_pos beta E _)
  have h1 := hpos true
  have h2 := hpos false
  cases m₀ <;> linarith

/-! ## A concrete erasure protocol (non-vacuity of the hypothesis below)

Swapping the memory bit with a bath bit leaves the memory in the bath's Gibbs state.
Taking the bath to be a two-level system with a large energy gap makes the erasure
error `gibbs beta E (!m₀)` as small as desired, so the hypothesis `1 - eps ≤ finalMem ...`
of `Phys.landauer_principle` is satisfiable with small `eps`. -/

