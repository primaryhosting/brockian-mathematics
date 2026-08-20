/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Polynomial Matrix Complex

/-- A primitive 10-th root of unity. -/

lemma w_pow_add_inv (k : Fin 10) :
    w ^ (k : ℕ) + (w ^ (k : ℕ))⁻¹ = (huckelEigenvalue k : ℂ) := by
  have h : w ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 10 : ℝ) * Complex.I) := by
    rw [w, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [h, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, huckelEigenvalue]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Expansion of one row of the adjacency matrix of `C₁₀` against the geometric vector
`j ↦ z ^ j`, for `z` a 10-th root of unity. -/
