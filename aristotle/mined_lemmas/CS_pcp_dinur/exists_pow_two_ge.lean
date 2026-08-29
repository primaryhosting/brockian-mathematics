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
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- `iter f t g` is the `t`-fold iterate `f^[t] g`. -/

theorem exists_pow_two_ge (m : Nat) (hm : 1 ≤ m) : ∃ t : Nat, m ≤ 2 ^ t ∧ 2 ^ t < 2 * m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact ⟨0, by omega, by omega⟩
    · obtain ⟨t, h1, h2⟩ := ih h
      by_cases hc : m + 1 ≤ 2 ^ t
      · exact ⟨t, hc, by omega⟩
      · have hEq : 2 ^ t = m := by omega
        refine ⟨t + 1, ?_, ?_⟩ <;> rw [Nat.pow_succ] <;> omega

/-- Doubling the scaled unsat value: `2 ^ (t + 1) * u = 2 * (2 ^ t * u)`. -/
