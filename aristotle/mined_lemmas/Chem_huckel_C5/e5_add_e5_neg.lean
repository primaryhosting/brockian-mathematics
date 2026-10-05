/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma e5_add_e5_neg (k : ZMod 5) : e5 k + e5 (-k) = huckelEigenvalue k := by
  have hz : e5 k = Complex.exp (((2 * Real.pi * k.val / 5 : ℝ) : ℂ) * Complex.I) := by
    rw [e5, zeta5, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzn : e5 (-k) = Complex.exp (-((2 * Real.pi * k.val / 5 : ℝ) : ℂ) * Complex.I) := by
    rw [e5_neg, hz, ← Complex.exp_neg]
    congr 1
    ring
  rw [hz, hzn, huckelEigenvalue, Complex.ofReal_cos, ← Complex.two_cos]

/-! ### Orthogonality -/

