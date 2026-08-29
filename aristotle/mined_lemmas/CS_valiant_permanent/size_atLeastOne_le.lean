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

lemma size_atLeastOne_le (m : ℕ) (f : Fin m → Circuit ι) (B : ℕ) (hf : ∀ a, (f a).size ≤ B) :
    (atLeastOne m f).size ≤ 1 + m * (1 + B) := by
  refine le_trans (size_bigOr_le _ B ?_) ?_
  · intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨a, -, rfl⟩ := hc
    exact hf a
  · simp

