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

lemma zeta_add_zeta_neg (k : ZMod 10) :
    zeta k + zeta (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 10) : ℝ) : ℂ) := by
  have hz : zeta k = Complex.exp ((2 * Real.pi * (k.val : ℝ) / 10 : ℝ) * Complex.I) := by
    rw [zeta, w, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz' : zeta (-k) = Complex.exp (-((2 * Real.pi * (k.val : ℝ) / 10 : ℝ) * Complex.I)) := by
    have h := zeta_mul_neg k
    have hinv : zeta (-k) = (zeta k)⁻¹ := (DivisionMonoid.inv_eq_of_mul _ _ h).symm
    rw [hinv, hz, ← Complex.exp_neg]
  have hcast : ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 10) : ℝ) : ℂ)
      = 2 * Complex.cos ((2 * Real.pi * (k.val : ℝ) / 10 : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_cos]
    ring
  rw [hz, hz', hcast, Complex.cos, neg_mul]
  ring

/-- **Hückel theory for the cycle `C₁₀`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₀` if and only if `μ = 2 cos (2 π k / 10)` for some
`k ∈ {0, …, 9}`. -/
