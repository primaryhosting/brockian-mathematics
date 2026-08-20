/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with vertices indexed by `ZMod n`:
vertex `i` is joined to `i + 1` and to `i - 1`.  For `n ≥ 3` this is exactly the adjacency matrix
of the simple cycle graph `C n`; for `n = 1, 2` it is the circulant matrix `S + S⁻¹` (`S` the
cyclic shift), which is the convention under which the Hückel spectrum formula holds. -/

lemma chi_add_chi_neg (n : ℕ) [NeZero n] (k : ZMod n) :
    chi n k + chi n (-k) = 2 * (Real.cos (2 * Real.pi * k.val / n) : ℂ) := by
  have hz : chi n k = Complex.exp (((2 * Real.pi * k.val / n : ℝ) : ℂ) * Complex.I) := by
    rw [chi, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [chi_neg, hz, Complex.ofReal_cos, Complex.two_cos, ← Complex.exp_neg]
  ring_nf

/-- **Hückel spectrum of the cycle `C n`.**  A complex number `lam` is an eigenvalue of the
adjacency (Hückel) matrix of the cycle graph on `n` vertices if and only if it is of the form
`2 * cos (2 π k / n)` for some `k = 0, …, n - 1`. -/
