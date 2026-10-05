/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

theorem card_eq_four_sorted {α : Type*} [LinearOrder α] {s : Finset α} (h : s.card = 4) :
    ∃ a b c d : α, a < b ∧ b < c ∧ c < d ∧ s = {a, b, c, d} := by
  have hlen : (s.sort (· ≤ ·)).length = 4 := by rw [Finset.length_sort, h]
  have hsorted := (Finset.sortedLT_sort s).pairwise
  have htf : (s.sort (· ≤ ·)).toFinset = s := Finset.sort_toFinset s _
  set l := s.sort (· ≤ ·) with hl
  match l, hlen with
  | [a, b, c, d], _ =>
    refine ⟨a, b, c, d, ?_, ?_, ?_, ?_⟩ <;> simp [List.pairwise_cons] at hsorted <;>
      first
        | tauto
        | (rw [← htf]; simp)

section Upper

variable {V : Type*} [LinearOrder V]

/-- `RamF G T p q` : inside the vertex set `T` there is either a `p`-clique of `G`
or a `q`-clique of the complement of `G`. -/
