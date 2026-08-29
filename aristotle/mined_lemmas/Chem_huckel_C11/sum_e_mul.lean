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

lemma sum_e_mul {m : ZMod 11} (hm : m ≠ 0) : ∑ l : ZMod 11, e (l * m) = 0 := by
  rw [← sum_e]
  exact Fintype.sum_equiv (Equiv.mulRight₀ m hm) _ _ (fun l => rfl)

/-! ## Diagonalisation by the discrete Fourier transform -/

/-- The `k`-th Hückel eigenvalue, as `ω^k + ω^{-k}`. -/
