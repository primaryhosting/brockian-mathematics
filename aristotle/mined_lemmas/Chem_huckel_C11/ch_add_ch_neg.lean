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

lemma ch_add_ch_neg (k : ZMod 11) : ch k + ch (-k) = eig k := by
  have h1 : ch k = Complex.exp ((↑(2 * Real.pi * k.val / 11) : ℂ) * Complex.I) := by
    rw [ch_apply]
    congr 1
    push_cast
    ring
  have h2 : ch (-k) = Complex.exp (-(↑(2 * Real.pi * k.val / 11) : ℂ) * Complex.I) := by
    have : ch (-k) = (ch k)⁻¹ := AddChar.map_neg_eq_inv _ _
    rw [this, h1, ← Complex.exp_neg]
    congr 1
    ring
  rw [h1, h2, eig, ← Complex.two_cos, Complex.ofReal_cos]

/-- Orthogonality: `∑ i, ch (t * i) = 11` if `t = 0`, and `0` otherwise. -/
