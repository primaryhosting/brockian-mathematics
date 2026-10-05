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

theorem permanent_inSharpP : permanentProblem.InSharpP := by
  refine ⟨fun n => n * n, fun n => permVerifier n, ⟨1, 2, fun n => ?_⟩, ⟨32, 3, ?_⟩, ?_⟩
  · nlinarith [sq_nonneg n]
  · exact fun n => size_permVerifier_le n
  · intro n x
    show (decodeMatrix n x).permanent = _
    rw [permanent_eq_card_perm (decodeMatrix n x) (fun i j => by
      simp only [decodeMatrix, Matrix.of_apply]
      split <;> simp)]
    rw [← card_witnesses n x]
    congr 1
    apply congrArg
    funext σ
    simp only [decodeMatrix, Matrix.of_apply, eq_iff_iff]
    constructor
    · intro h i
      have := h i
      split at this
      · assumption
      · simp at this
    · intro h i
      rw [if_pos (h i)]

/-! ## Part C: eliminating weights, i.e. `0/1` permanents simulate `ℕ`-weighted permanents -/

/-- The permanent is invariant under simultaneous reindexing of rows and columns. -/
