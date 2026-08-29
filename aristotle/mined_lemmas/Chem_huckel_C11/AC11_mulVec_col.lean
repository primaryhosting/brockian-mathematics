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

lemma AC11_mulVec_col (k : ZMod 11) :
    AC11 *ᵥ (fun j => F j k) = lam k • (fun j => F j k) := by
  funext j
  rw [AC11_mulVec]
  show e ((j - 1) * k) + e ((j + 1) * k) = lam k * e (j * k)
  rw [show (j - 1) * k = j * k + -k by ring, show (j + 1) * k = j * k + k by ring,
    e_add, e_add, lam]
  ring

