import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

set_option grind.warning false

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The "centered indicator" of a finite set `S`: the indicator of `S` minus its mean value.
It is orthogonal to the all-ones vector. -/

lemma sum_sq_centeredIndicator (hV : (Fintype.card V) ≠ 0) (S : Finset V) :
    ∑ i, (centeredIndicator S i) ^ 2
      = S.card - (S.card : ℝ) ^ 2 / (Fintype.card V) := by
  have hn : ((Fintype.card V : ℝ)) ≠ 0 := by exact_mod_cast hV
  have hpt : ∀ i : V, (centeredIndicator S i) ^ 2
      = (if i ∈ S then (1:ℝ) else 0)
        - 2 * ((S.card : ℝ) / (Fintype.card V)) * (if i ∈ S then (1:ℝ) else 0)
        + ((S.card : ℝ) / (Fintype.card V)) ^ 2 := by
    intro i
    by_cases h : i ∈ S
    · simp only [centeredIndicator, h, if_true]; ring
    · simp only [centeredIndicator, h, if_false]; ring
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Finset.card_univ]
  field_simp
  ring

