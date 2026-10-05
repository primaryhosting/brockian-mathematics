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

lemma AC11_mul_F : AC11 * F = F * Matrix.diagonal lam := by
  ext j k
  have h1 : (AC11 * F) j k = (AC11 *ᵥ (fun l => F l k)) j := rfl
  rw [h1, AC11_mulVec_col, Matrix.mul_diagonal]
  simp [mul_comm]

