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

lemma jointProb_total : ∑ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool, jointProb f A a b = 1 := by
  have hN : (Fintype.card (V → Bool) : ℝ) ≠ 0 := ne_of_gt (card_pos_real (V := V))
  have hpt : ∀ x : V → Bool, ∑ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool,
      (if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0) = 1 := by
    intro x
    simp [ite_and]
  simp only [jointProb, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hN]
  calc (∑ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool, ∑ x : V → Bool,
          (if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0))
      = ∑ a : ↥A → Bool, ∑ x : V → Bool, ∑ b : ↥Aᶜ → Bool,
          (if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x : V → Bool, ∑ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool,
          (if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ _x : V → Bool, (1 : ℝ) := Finset.sum_congr rfl fun x _ => hpt x
    _ = (Fintype.card (V → Bool) : ℝ) := by simp

