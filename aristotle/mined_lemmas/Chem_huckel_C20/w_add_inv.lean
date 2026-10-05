import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

set_option grind.warning false

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma w_add_inv (k : Fin 20) : w ^ (k : ℕ) + w ^ (19 * (k : ℕ)) = hval k := by
  have hwk : w ^ (k : ℕ)
      = Complex.exp (((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
    rw [w, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h19 : w ^ (k : ℕ) * w ^ (19 * (k : ℕ)) = 1 := by
    rw [← pow_add, show (k : ℕ) + 19 * (k : ℕ) = 20 * (k : ℕ) by ring, pow_mul, w_pow_20,
      one_pow]
  have hne : w ^ (k : ℕ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h19
    exact zero_ne_one h19
  have hinv : w ^ (19 * (k : ℕ)) = (w ^ (k : ℕ))⁻¹ := by
    field_simp
    linear_combination h19
  have hcos : hval k = 2 * Complex.cos (((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ)) := by
    rw [hval, ← Complex.ofReal_cos]
    push_cast
    ring
  rw [hinv, hwk, ← Complex.exp_neg, hcos, Complex.two_cos, neg_mul]

