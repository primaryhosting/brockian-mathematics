import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
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

open Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid. -/

theorem charPoly_freeOn_eq_pow [Fintype α] :
    charPoly (Matroid.freeOn (Set.univ : Set α)) = (X - 1) ^ (Fintype.card α) := by
  set n := Fintype.card α with hn
  rw [charPoly_freeOn]
  have h : ((X : Polynomial ℤ) - 1) ^ n = (X + (-1)) ^ n := by ring
  rw [h, add_pow, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp only [Finset.mem_range] at hk
  have hk' : k ≤ n := by omega
  have h0 : n + 1 - 1 - k = n - k := by omega
  have h1 : n - (n - k) = k := by omega
  rw [h0, h1, Nat.choose_symm hk']
  ring

