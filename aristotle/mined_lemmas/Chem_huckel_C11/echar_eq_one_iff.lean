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

lemma echar_eq_one_iff (x : Fin 11) : echar x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have hdvd := (isPrimitiveRoot_zeta11.pow_eq_one_iff_dvd (x : ℕ)).1 h
    have hx : (x : ℕ) < 11 := x.isLt
    have hx0 : (x : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hx
    exact Fin.ext (by simpa using hx0)
  · rintro rfl; exact echar_zero

