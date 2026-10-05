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

lemma AC11_sub_smul_one (mu : ℂ) :
    AC11 - mu • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)
      = F * (Matrix.diagonal lam - mu • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)) * Finv := by
  rw [Matrix.mul_sub, Matrix.sub_mul, ← AC11_mul_F, Matrix.mul_assoc,
    F_mul_Finv, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, F_mul_Finv]

