/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The adjacency eigenvalues of the cycle graph `C_10` are exactly the numbers
`2 * cos (2 * π * k / 10)` for `k = 0, …, 9`.

We index the vertices of `C₁₀` by `ZMod 10`, so that the adjacency matrix is
`C10adj i j = 1` iff `i` and `j` differ by `1`.  The eigenvectors are the discrete
Fourier modes `j ↦ ζ (k * j)` where `ζ a = exp (2 π i a / 10)`.
-/

namespace Chem

open Finset

/-- A primitive 10-th root of unity. -/

lemma mulVec_apply (v : ZMod 10 → ℂ) (i : ZMod 10) :
    C10adj.mulVec v i = v (i + 1) + v (i - 1) := by
  have hne : (i - 1 : ZMod 10) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 10) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 10, C10adj i j * v j
      = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    have h1 : (i - j = 1) ↔ (j = i - 1) := by
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring
    have h2 : (j - i = 1) ↔ (j = i + 1) := by
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring
    by_cases hb : j = i + 1
    · subst hb
      have hA : C10adj i (i + 1) = 1 := by
        simp only [C10adj, Matrix.of_apply]
        rw [if_pos]
        right; ring
      rw [hA, one_mul, if_pos rfl, if_neg (fun h => hne h.symm), add_zero]
    · by_cases hc : j = i - 1
      · subst hc
        have hA : C10adj i (i - 1) = 1 := by
          simp only [C10adj, Matrix.of_apply]
          rw [if_pos]
          left; ring
        rw [hA, one_mul, if_neg hb, if_pos rfl, zero_add]
      · have hA : C10adj i j = 0 := by
          simp only [C10adj, Matrix.of_apply]
          rw [if_neg]
          rintro (h | h)
          · exact hc (h1.mp h)
          · exact hb (h2.mp h)
        rw [hA, zero_mul, if_neg hb, if_neg hc, add_zero]
  rw [Matrix.mulVec, dotProduct]
  simp only [key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- The eigenvalue attached to the `k`-th Fourier mode. -/
