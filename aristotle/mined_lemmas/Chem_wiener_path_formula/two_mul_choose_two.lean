import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset SimpleGraph

/-- The Wiener index of a finite graph: the sum of the distances over all unordered
pairs of vertices. -/

lemma two_mul_choose_two (n : ℕ) : 2 * (n + 1).choose 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ' (n + 1) 1]
    simp only [Nat.choose_one_right] at *
    ring_nf
    ring_nf at ih
    omega

/-- Key intermediate lemma: the sum of all pairwise distances (over ordered pairs) in the
path graph `P n` is `2 * C(n+1, 3)`. -/
