import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem chi_add_neg (k : ZMod 10) : chi k + chi (-k) = C10eigen k := by
  have hk : chi k = Complex.exp ((2 * Real.pi * k.val / 10 : ℝ) * Complex.I) := by
    rw [chi, om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [C10eigen, chi_neg, hk, Complex.ofReal_cos, Complex.two_cos, ← Complex.exp_neg]
  congr 2
  ring

