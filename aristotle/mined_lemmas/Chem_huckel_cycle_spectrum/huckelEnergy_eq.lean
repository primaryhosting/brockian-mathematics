import Mathlib

/-!
# Hückel π-energies of the cycle graph `C n`

The adjacency (Hückel) matrix of the cycle graph `C n` (`n ≥ 3`) has spectrum
`{2 cos (2 π k / n) : k = 0, …, n-1}`, and its characteristic polynomial is
`∏ k, (X - 2 cos (2 π k / n))`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma huckelEnergy_eq {n k : ℕ} (hn : n ≠ 0) :
    ((huckelEnergy n k : ℝ) : ℂ) = cycleRoot n ^ k + (cycleRoot n ^ k)⁻¹ := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpow : cycleRoot n ^ k = Complex.exp (((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
    rw [cycleRoot, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [hpow, huckelEnergy, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

