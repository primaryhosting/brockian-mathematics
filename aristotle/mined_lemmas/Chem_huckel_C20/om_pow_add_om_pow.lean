/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma om_pow_add_om_pow (k : Fin 20) :
    om ^ (k : ℕ) + om ^ (19 * (k : ℕ)) = eval20 k := by
  set x : ℝ := 2 * Real.pi * (k : ℕ) / 20 with hx
  have h1 : om ^ (k : ℕ) = Complex.exp ((x : ℂ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul, hx]
    push_cast
    ring_nf
  have hmul : om ^ (19 * (k : ℕ)) * om ^ (k : ℕ) = 1 := by
    rw [← pow_add, show 19 * (k : ℕ) + (k : ℕ) = 20 * (k : ℕ) from by ring, pow_mul,
      om_pow_20, one_pow]
  have h2 : om ^ (19 * (k : ℕ)) = Complex.exp (-(x : ℂ) * Complex.I) := by
    rw [eq_inv_of_mul_eq_one_left hmul, h1, ← Complex.exp_neg]
    ring_nf
  rw [eval20, h1, h2, Complex.ofReal_mul, Complex.ofReal_cos]
  push_cast
  rw [Complex.two_cos, hx]
  push_cast
  ring_nf

