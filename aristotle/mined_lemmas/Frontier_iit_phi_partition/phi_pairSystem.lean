/-
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite *system*: a set of elements `V` together with nonnegative directed
interaction strengths `w u v` between them. -/
structure System (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Strength of the (directed) causal influence of `u` on `v`. -/
  w : V → V → ℝ
  /-- Interaction strengths are nonnegative. -/
  w_nonneg : ∀ u v, 0 ≤ w u v

/-- The *effective information* across the bipartition `(A, Aᶜ)` of a system:
the total interaction strength that is severed when the system is cut into the
two parts `A` and `Aᶜ`. -/

theorem phi_pairSystem : phi pairSystem = 2 := by
  have hT : ({true} : Finset Bool)ᶜ = {false} := by ext y; cases y <;> simp
  have hF : ({false} : Finset Bool)ᶜ = {true} := by ext y; cases y <;> simp
  have hval : effInfoValues pairSystem = {2} := by
    ext x
    constructor
    · rintro ⟨A, hA, rfl⟩
      have hcases : A = {true} ∨ A = {false} := by
        revert hA; unfold IsProper; revert A; decide
      rcases hcases with rfl | rfl
      · simp [effInfo, pairSystem, hT]
        norm_num
      · simp [effInfo, pairSystem, hF]
        norm_num
    · rintro rfl
      refine ⟨{true}, ⟨⟨true, by simp⟩, ⟨false, by simp⟩⟩, ?_⟩
      simp [effInfo, pairSystem, hT]
      norm_num
  simp [phi, hval]

end Examples

end Frontier

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

