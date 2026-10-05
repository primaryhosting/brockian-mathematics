import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
-- `open scoped Classical` is omitted here: it overrides the graph's own `DecidableRel`
-- instances and makes `if`-congruence rewriting fail below.
-- open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open SimpleGraph Matrix Finset

section Combinatorics

variable {m : ℕ}

/-- Adjacency in the cycle graph on `Fin (m+1)` (with `m ≥ 2`) in additive form. -/

lemma cycle_sum_adj (hm : 2 ≤ m) (x : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∑ j, (if (cycleGraph (m + 1)).Adj i j then x j else 0) = x (i + 1) + x (i - 1) := by
  have hne : i + 1 ≠ i - 1 := succ_ne_pred hm i
  have hsplit : ∀ j : Fin (m + 1), (if (cycleGraph (m + 1)).Adj i j then x j else 0)
      = (if j = i + 1 then x j else 0) + (if j = i - 1 then x j else 0) := by
    intro j
    have hiff := cycleGraph_adj_iff hm i j
    have hj : (i = j + 1) ↔ (j = i - 1) := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [h]; simp
    by_cases h1 : j = i + 1
    · have hA : (cycleGraph (m + 1)).Adj i j := hiff.mpr (Or.inl h1)
      have h2 : j ≠ i - 1 := by rw [h1]; exact hne
      rw [if_pos hA, if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : j = i - 1
      · have hA : (cycleGraph (m + 1)).Adj i j := hiff.mpr (Or.inr (hj.mpr h2))
        rw [if_pos hA, if_neg h1, if_pos h2, zero_add]
      · have hA : ¬ (cycleGraph (m + 1)).Adj i j := by
          intro hA
          rcases hiff.mp hA with h | h
          · exact h1 h
          · exact h2 (hj.mp h)
        rw [if_neg hA, if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  simp

/-- The degree of every vertex of the cycle graph `C_{m+1}` (`m ≥ 2`) is `2`. -/
