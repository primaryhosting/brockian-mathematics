/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the graph distances over all
unordered pairs of vertices (equivalently, half the sum over all ordered pairs). -/

lemma two_mul_sum_succ (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring

