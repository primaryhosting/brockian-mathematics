import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a finite graph: the sum of the graph distances over all unordered
pairs of vertices.  It is computed here as half of the sum of `G.dist u v` over all ordered
pairs `(u, v)`. -/

theorem sum_natDist_top (n : ℕ) :
    ∑ i ∈ range n, Nat.dist i n = Nat.choose (n + 1) 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hstep : ∑ i ∈ range n, Nat.dist i (n + 1)
          = (∑ i ∈ range n, Nat.dist i n) + n := by
        have hcongr : ∀ i ∈ range n, Nat.dist i (n + 1) = Nat.dist i n + 1 := by
          intro i hi
          simp only [Finset.mem_range] at hi
          unfold Nat.dist
          omega
        rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, smul_eq_mul, mul_one]
      have hlast : Nat.dist n (n + 1) = 1 := by unfold Nat.dist; omega
      have hc2 : Nat.choose (n + 1 + 1) 2 = Nat.choose (n + 1) 1 + Nat.choose (n + 1) 2 := rfl
      rw [hstep, ih, hlast]
      simp only [Nat.choose_one_right] at hc2
      omega

/-- `∑_{i,j < n} |i - j| = 2 · C(n+1, 3)`. -/
