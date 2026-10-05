import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

lemma eval_atMostOne (m : ℕ) (f : Fin m → Circuit ι) (v : ι → Bool) :
    (atMostOne m f).eval v = true ↔ ∀ a b, (f a).eval v = true → (f b).eval v = true → a = b := by
  rw [atMostOne, eval_bigAnd]
  constructor
  · intro h a b ha hb
    by_contra hab
    have := h (neg (conj (f a) (f b))) (by
      simp only [List.mem_flatMap]
      exact ⟨a, List.mem_finRange a, by
        simp only [List.mem_map]
        exact ⟨b, List.mem_finRange b, by rw [if_neg hab]⟩⟩)
    simp [eval, ha, hb] at this
  · intro h c hc
    simp only [List.mem_flatMap, List.mem_map] at hc
    obtain ⟨a, -, b, -, rfl⟩ := hc
    by_cases hab : a = b
    · simp [hab, eval]
    · simp only [if_neg hab, eval, Bool.not_eq_true', Bool.and_eq_false_iff]
      by_cases ha : (f a).eval v = true
      · by_cases hb : (f b).eval v = true
        · exact absurd (h a b ha hb) hab
        · simp [hb]
      · simp [ha]

