/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-! ### A primitive 7th root of unity -/

/-- A primitive 7th root of unity. -/

lemma lam7_eq (k : Fin 7) :
    lam7 k = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 7 with ht
  have h1 : w7 ^ (k : ℕ) = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [w7, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have hmul : w7 ^ (6 * (k : ℕ)) * w7 ^ (k : ℕ) = 1 := by
    rw [← pow_add, show 6 * (k : ℕ) + (k : ℕ) = 7 * (k : ℕ) by ring, pow_mul, w7_pow_seven,
      one_pow]
  have h2 : w7 ^ (6 * (k : ℕ)) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [Complex.exp_neg, ← h1]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [lam7, h1, h2,
    show Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-((t : ℂ) * Complex.I))
      = 2 * Complex.cos (t : ℂ) by rw [Complex.cos]; ring_nf]
  push_cast
  rfl

