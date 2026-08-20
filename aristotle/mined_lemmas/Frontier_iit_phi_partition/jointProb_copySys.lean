/-
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

set_option grind.warning false

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The restriction of a global state `x` to the part `A` of the system. -/

lemma jointProb_copySys (a : ↥leftPart → Bool) (b : ↥leftPartᶜ → Bool) :
    jointProb copySys leftPart a b = if a default = b default then 1 / 2 else 0 := by
  have hcard : (Fintype.card (Fin 2 → Bool) : ℝ) = 4 := by simp
  have hnum : (∑ x : Fin 2 → Bool,
      if restr leftPart (copySys x) = a ∧ restr leftPartᶜ (copySys x) = b then (1 : ℝ) else 0)
      = if a default = b default then 2 else 0 := by
    have hpt : ∀ x : Fin 2 → Bool,
        (if restr leftPart (copySys x) = a ∧ restr leftPartᶜ (copySys x) = b then (1 : ℝ) else 0)
          = (fun c : Bool => if c = a default ∧ c = b default then (1 : ℝ) else 0) (x 0) := by
      intro x
      have h1 : (restr leftPart (copySys x) = a) ↔ x 0 = a default := const_eq_iff (x 0) a
      have h2 : (restr leftPartᶜ (copySys x) = b) ↔ x 0 = b default := const_eq_iff (x 0) b
      simp only [h1, h2]
    refine (Finset.sum_congr rfl fun x _ => hpt x).trans
      ((sum_fin2_first fun c : Bool => if c = a default ∧ c = b default then (1 : ℝ) else 0).trans
        ?_)
    cases hA : a default <;> cases hB : b default <;> norm_num
  rw [jointProb, hnum, hcard]
  by_cases h : a default = b default <;> norm_num [h]

