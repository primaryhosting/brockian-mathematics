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

lemma size_permVerifier_le (n : ℕ) : (permVerifier n).size ≤ 32 * (n + 1) ^ 3 := by
  have hE : ∀ f : Fin n → Circuit (Fin (n * n) ⊕ Fin (n * n)), (∀ a, (f a).size = 1) →
      (Circuit.exactlyOne n f).size ≤ 3 + n * 2 + (n * n) * 5 := by
    intro f hf
    have h := Circuit.size_exactlyOne_le n f 1 (fun a => le_of_eq (hf a))
    norm_num at h ⊢
    omega
  have hrows : (Circuit.bigAnd ((List.finRange n).map fun i =>
      Circuit.exactlyOne n (fun j => yvar n i j))).size ≤
      1 + n * (1 + (3 + n * 2 + (n * n) * 5)) := by
    refine le_trans (Circuit.size_bigAnd_le _ (3 + n * 2 + (n * n) * 5) ?_) ?_
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨i, -, rfl⟩ := hc
      exact hE _ (fun _ => rfl)
    · simp
  have hcols : (Circuit.bigAnd ((List.finRange n).map fun j =>
      Circuit.exactlyOne n (fun i => yvar n i j))).size ≤
      1 + n * (1 + (3 + n * 2 + (n * n) * 5)) := by
    refine le_trans (Circuit.size_bigAnd_le _ (3 + n * 2 + (n * n) * 5) ?_) ?_
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨j, -, rfl⟩ := hc
      exact hE _ (fun _ => rfl)
    · simp
  have hsupp : (Circuit.bigAnd ((List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
      Circuit.disj (Circuit.neg (yvar n i j)) (xvar n i j))).size ≤ 1 + (n * n) * 5 := by
    refine le_trans (Circuit.size_bigAnd_le _ 4 ?_) ?_
    · intro c hc
      simp only [List.mem_flatMap, List.mem_map] at hc
      obtain ⟨i, -, j, -, rfl⟩ := hc
      exact le_of_eq rfl
    · simp [List.length_flatMap]
  simp only [permVerifier, Circuit.size]
  nlinarith [hrows, hcols, hsupp, Nat.zero_le n]

/-- The witness (permutation matrix) associated with a permutation. -/
