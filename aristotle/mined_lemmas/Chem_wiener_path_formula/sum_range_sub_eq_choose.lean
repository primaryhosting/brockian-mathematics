/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices, i.e. half the sum of `dist u v` over all ordered pairs. -/

theorem sum_range_sub_eq_choose (n : ℕ) :
    ∑ i ∈ Finset.range n, (n - i) = Nat.choose (n + 1) 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ']
      have : ∀ i ∈ Finset.range n, (n + 1 - (i + 1)) = n - i := by
        intro i _; omega
      rw [Finset.sum_congr rfl this, ih]
      simp [Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right]
      omega

/-- The double sum of `Nat.dist` over `range n` equals `2 * C(n+1, 3)`. -/
