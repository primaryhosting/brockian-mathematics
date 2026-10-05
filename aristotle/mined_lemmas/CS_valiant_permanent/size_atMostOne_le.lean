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

lemma size_atMostOne_le (m : ℕ) (f : Fin m → Circuit ι) (B : ℕ) (hf : ∀ a, (f a).size ≤ B) :
    (atMostOne m f).size ≤ 1 + (m * m) * (3 + 2 * B) := by
  refine le_trans (size_bigAnd_le _ (2 + 2 * B) ?_) ?_
  · intro c hc
    simp only [List.mem_flatMap, List.mem_map] at hc
    obtain ⟨a, -, b, -, rfl⟩ := hc
    by_cases hab : a = b
    · simp only [if_pos hab, size]
      omega
    · have ha := hf a
      have hb := hf b
      simp only [if_neg hab, size]
      omega
  · have hlen : ((List.finRange m).flatMap fun a => (List.finRange m).map fun b =>
        if a = b then (tru : Circuit ι) else neg (conj (f a) (f b))).length = m * m := by
      simp [List.length_flatMap]
    have h4 : (1 : ℕ) + (2 + 2 * B) = 3 + 2 * B := by ring
    rw [hlen, h4]

