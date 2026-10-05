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

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Brockian.Weyl.WeylLawTarget

variable {α : Type u}

/-- `countingFunction lam L K` is the number of indices `n < K` whose eigenvalue `lam n`
lies at or below the threshold `L`.  For a discrete spectrum this stabilises as `K → ∞`
and its limiting value is the Weyl counting function `N(L) = #{n | lam n ≤ L}`. -/

theorem countingFunction_eq_card (lam : ℕ → ℝ) (Λ : ℝ) (K : ℕ) :
    countingFunction lam Λ K = ((Finset.range K).filter (fun n => lam n ≤ Λ)).card := by
  induction K with
  | zero => simp [countingFunction]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : lam n ≤ Λ
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp [countingFunction, ih, h]
    · rw [if_neg h]
      simp [countingFunction, ih, h]

/-- Real discreteness implies the abstract discreteness hypothesis of the target theorem. -/
