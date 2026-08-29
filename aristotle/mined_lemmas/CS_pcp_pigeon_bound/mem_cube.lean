import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace CS

/-- The finite set of all binary strings (lists of booleans) of length `n`. -/

@[simp] lemma mem_cube {n : ℕ} {u : List Bool} : u ∈ cube n ↔ u.length = n := by
  induction n generalizing u with
  | zero => simp [cube, List.length_eq_zero_iff]
  | succ n ih =>
      cases u with
      | nil => simp [cube]
      | cons b u =>
          cases b <;> simp [cube, ih]

