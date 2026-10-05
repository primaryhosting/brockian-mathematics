/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for the cycle C₁₁

The adjacency eigenvalues of the cycle graph `C₁₁` are exactly `2 cos (2πk/11)`, `k = 0,…,10`.
-/

open Complex Matrix Finset

namespace Chem

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-! ## The cycle graph and its adjacency matrix -/

/-- The cycle graph on 11 vertices, realised on `ZMod 11`: `i ~ j` iff `i - j = ±1`. -/

lemma lam_eq (k : ZMod 11) : lam k = 2 * Real.cos (2 * Real.pi * k.val / 11) := by
  have hk : e k = Complex.exp ((2 * Real.pi * k.val / 11 : ℝ) * Complex.I) := by
    rw [e, om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnk : e (-k) = Complex.exp ((-(2 * Real.pi * k.val / 11) : ℝ) * Complex.I) := by
    rw [e_neg, hk, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [lam, hk, hnk, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The discrete Fourier matrix; its `k`-th column is the `k`-th eigenvector. -/
