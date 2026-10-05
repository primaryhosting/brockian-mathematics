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

lemma sum_zeta (a : ZMod 10) : ∑ k : ZMod 10, zeta (k * a) = if a = 0 then 10 else 0 := by
  by_cases ha : a = 0
  · subst ha; simp [ZMod.card]
  · simp only [ha, if_false]
    set S : ℂ := ∑ k : ZMod 10, zeta (k * a) with hS
    have hshift : zeta a * S = S := by
      rw [hS, Finset.mul_sum]
      have h : ∀ k : ZMod 10, zeta a * zeta (k * a) = zeta ((k + 1) * a) := by
        intro k
        rw [← zeta_add]
        ring_nf
      rw [Finset.sum_congr rfl fun k _ => h k]
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod 10)) (fun k => zeta (k * a))
    have h1 : zeta a ≠ 1 := fun h => ha ((zeta_eq_one_iff a).mp h)
    have hz : (zeta a - 1) * S = 0 := by rw [sub_mul, hshift, one_mul, sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (sub_eq_zero.mp h) h1
    · exact h

