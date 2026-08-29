import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/

lemma mu_eq (k : ZMod 13) : mu k = 2 * Real.cos (2 * Real.pi * k.val / 13) := by
  have hz : ee k = Complex.exp ((2 * Real.pi * k.val / 13 : ℝ) * Complex.I) := by
    rw [ee, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mu, ee_neg, hz, Complex.ofReal_cos, Complex.two_cos, ← Complex.exp_neg]
  ring_nf

/-- **Hückel theory for the cycle `C₁₃`.**  A complex number `lam` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₃` (i.e. there is a nonzero vector `v` with
`A v = lam v`) if and only if `lam = 2 cos (2 π k / 13)` for some `k = 0, …, 12`. -/
