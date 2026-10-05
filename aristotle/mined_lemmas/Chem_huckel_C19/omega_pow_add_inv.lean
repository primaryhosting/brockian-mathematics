import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

lemma omega_pow_add_inv (k : Fin 19) :
    omega19 ^ (k : ℕ) + (omega19 ^ (k : ℕ))⁻¹ = hueckelEigenvalue k := by
  have hexp : omega19 ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 19 : ℝ) * Complex.I) := by
    rw [omega19, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinv : (omega19 ^ (k : ℕ))⁻¹ =
      Complex.exp (-(2 * Real.pi * (k : ℕ) / 19 : ℝ) * Complex.I) := by
    rw [hexp, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hinv, hexp, ← Complex.two_cos, hueckelEigenvalue, Complex.ofReal_mul, Complex.ofReal_cos]
  push_cast
  ring

