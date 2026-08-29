import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex SimpleGraph Matrix

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma zeta_pow_eq_exp {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    zeta n ^ k = Complex.exp (((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
  have hn' : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- `ζ^k + ζ^{-k} = 2 cos(2πk/n)`: the Hückel energy level. -/
