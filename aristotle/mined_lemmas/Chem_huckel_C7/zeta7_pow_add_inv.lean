import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertex `i` is adjacent to `i + 1` and to `i - 1`. -/

lemma zeta7_pow_add_inv (k : ℕ) :
    zeta7 ^ k + (zeta7 ^ k)⁻¹ = 2 * Real.cos (2 * Real.pi * k / 7) := by
  rw [zeta7, ← Complex.exp_nat_mul]
  have h1 : (k : ℂ) * (2 * Real.pi * Complex.I / 7)
      = ((2 * Real.pi * k / 7 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- Every 7th root of unity `y` satisfies `y + y⁻¹ = 2 cos (2πk/7)` for some `k < 7`. -/
