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

lemma zeta_eq_one_iff (a : ZMod 10) : zeta a = 1 ↔ a = 0 := by
  rw [zeta, isPrimitiveRoot_w.pow_eq_one_iff_dvd]
  constructor
  · intro h
    exact (ZMod.val_eq_zero a).mp (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt a))
  · rintro rfl
    simp

