import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

namespace CycleAux

variable (m : ℕ)

/-- The primitive `(m+3)`-rd root of unity. -/

lemma sum_ee (a : Fin (m + 3)) :
    ∑ j : Fin (m + 3), ee m (a * j) = if a = 0 then ((m + 3 : ℕ) : ℂ) else 0 := by
  by_cases ha : a = 0
  · subst ha; simp [ee_zero]
  · rw [if_neg ha]
    have key : ee m a * ∑ j : Fin (m + 3), ee m (a * j) = ∑ j : Fin (m + 3), ee m (a * j) := by
      rw [Finset.mul_sum,
        ← Equiv.sum_comp (Equiv.addRight (1 : Fin (m + 3))) (fun j => ee m (a * j))]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Equiv.coe_addRight]
      rw [mul_add, ee_add, mul_one, mul_comm]
    have h1 : (ee m a - 1) * ∑ j : Fin (m + 3), ee m (a * j) = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) (fun hh => ha ((ee_eq_one_iff m a).1 hh))
    · exact h

