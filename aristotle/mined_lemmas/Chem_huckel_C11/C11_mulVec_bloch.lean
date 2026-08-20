import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₁`, with vertices indexed by `ZMod 11`:
vertex `i` is adjacent to `i + 1` and `i - 1`. -/

lemma C11_mulVec_bloch (k : ZMod 11) :
    C11 *ᵥ (fun j => ch (j * k)) = eig k • (fun j => ch (j * k)) := by
  funext i
  rw [C11_mulVec]
  have e1 : ch ((i + 1) * k) = ch (i * k) * ch k := by rw [← ch_add]; congr 1; ring
  have e2 : ch ((i - 1) * k) = ch (i * k) * ch (-k) := by rw [← ch_add]; congr 1; ring
  rw [e1, e2, ← mul_add, ch_add_ch_neg]
  simp [mul_comm]

/-- The characteristic determinant factors through the Hückel eigenvalues. -/
