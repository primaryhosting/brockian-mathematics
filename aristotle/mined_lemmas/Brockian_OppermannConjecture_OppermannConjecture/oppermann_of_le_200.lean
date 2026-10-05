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


theorem oppermann_of_le_200 (n : Nat) (hn : 1 < n) (hn' : n ≤ 200) :
    (∃ p : Nat, IsPrimeNat p ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : Nat, IsPrimeNat p ∧ n * n < p ∧ p < n * (n + 1)) := by
  have h := List.all_eq_true.mp oppermann_check_le_200 n (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with h | ⟨h1, h2⟩
  · omega
  · exact ⟨hasPrimeIn_spec h1, hasPrimeIn_spec h2⟩

/-! ## Conditional reduction -/

