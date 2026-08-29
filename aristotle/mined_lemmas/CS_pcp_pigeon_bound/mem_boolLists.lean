/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- The finset of all binary strings (lists of booleans) of length `n`. -/

lemma mem_boolLists {l : List Bool} {n : ℕ} : l ∈ boolLists n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [boolLists, List.length_eq_zero_iff]
  | succ n ih =>
    cases l with
    | nil => simp [boolLists]
    | cons b t =>
      have hlen : (b :: t).length = n + 1 ↔ t.length = n := by simp
      rw [hlen]
      simp only [boolLists, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and,
        List.cons.injEq]
      constructor
      · rintro ⟨b', l, hl, -, rfl⟩
        exact ih.1 hl
      · intro hl
        exact ⟨b, t, ih.2 hl, rfl, rfl⟩

