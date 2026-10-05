/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The hypercube and its signed adjacency operator -/

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a point of the Boolean hypercube. -/

lemma sgn_flipAt_of_gt {x : Fin n → Bool} {i j : Fin n} (h : i < j) :
    sgn (flipAt x i) j = - sgn x j := by
  set T : Finset (Fin n) := Finset.univ.filter (fun k => k < j ∧ x k = true) with hT
  set T' : Finset (Fin n) := Finset.univ.filter (fun k => k < j ∧ flipAt x i k = true) with hT'
  have key : ∀ k : Fin n, k ≠ i → (k ∈ T ↔ k ∈ T') := by
    intro k hk
    simp only [hT, hT', Finset.mem_filter, Finset.mem_univ, true_and,
      flipAt_apply_of_ne _ hk]
  by_cases hx : x i = true
  · have hiT : i ∈ T := by simp [hT, h, hx]
    have : T' = T.erase i := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp [hT', hx, h]
      · simp only [Finset.mem_erase, hk, ne_eq, not_false_eq_true, true_and]
        exact (key k hk).symm
    have hcard : T'.card = T.card - 1 := by rw [this, Finset.card_erase_of_mem hiT]
    have hpos : 1 ≤ T.card := Finset.card_pos.2 ⟨i, hiT⟩
    unfold sgn
    rw [← hT, ← hT', hcard]
    obtain ⟨m, hm⟩ : ∃ m, T.card = m + 1 := ⟨T.card - 1, by omega⟩
    rw [hm]
    simp [pow_succ]
  · have hx' : x i = false := by simpa using hx
    have hiT : i ∉ T := by simp [hT, hx']
    have : T' = insert i T := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp [hT', hx', h]
      · simp only [Finset.mem_insert, hk, false_or]
        exact (key k hk).symm
    have hcard : T'.card = T.card + 1 := by rw [this, Finset.card_insert_of_notMem hiT]
    unfold sgn
    rw [← hT, ← hT', hcard]
    simp [pow_succ]

