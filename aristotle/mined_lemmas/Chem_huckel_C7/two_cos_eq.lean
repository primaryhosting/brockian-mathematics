/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem two_cos_eq (k : ℕ) :
    ((2 * Real.cos (2 * Real.pi * k / 7) : ℝ) : ℂ) = zeta ^ k + (zeta ^ k)⁻¹ := by
  have hz : zeta ^ k = Complex.exp (2 * Real.pi * k * Complex.I / 7) := by
    rw [zeta, ← Complex.exp_nat_mul]; ring_nf
  rw [hz, ← Complex.exp_neg]
  push_cast
  have h : Complex.cos (2 * (Real.pi : ℂ) * k / 7)
      = (Complex.exp ((2 * (Real.pi : ℂ) * k / 7) * Complex.I)
        + Complex.exp (-(2 * (Real.pi : ℂ) * k / 7) * Complex.I)) / 2 := by
    rw [Complex.cos]
  rw [h, show (2 * (Real.pi : ℂ) * k / 7) * Complex.I = 2 * Real.pi * k * Complex.I / 7 by ring,
    show (-(2 * (Real.pi : ℂ) * k / 7)) * Complex.I = -(2 * Real.pi * k * Complex.I / 7) by ring]
  ring

/-! ### The eigenvectors -/

/-- The Fourier eigenvector `j ↦ ζ^(k j)`. -/
