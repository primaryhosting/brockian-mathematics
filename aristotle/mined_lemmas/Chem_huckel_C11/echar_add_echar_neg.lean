/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

lemma echar_add_echar_neg (k : Fin 11) :
    echar k + echar (-k) = huckelEigenvalue k := by
  have hk : echar k = Complex.exp ((((2 * Real.pi * (k : ℕ) / 11 : ℝ)) : ℂ) * Complex.I) := by
    rw [echar, zeta11, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnk : echar (-k) = Complex.exp (-(((2 * Real.pi * (k : ℕ) / 11 : ℝ)) : ℂ) * Complex.I) := by
    rw [echar_neg, hk, ← Complex.exp_neg]
    congr 1
    ring
  rw [hk, hnk, huckelEigenvalue]
  push_cast
  rw [Complex.cos]
  ring

