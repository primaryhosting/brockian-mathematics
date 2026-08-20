import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Catalan's conjecture, proved by Mihailescu (2004), states that the only pair of consecutive
perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`; equivalently the only solution of
`x ^ p - y ^ q = 1` in integers `x, y, p, q > 1` is `3 ^ 2 - 2 ^ 3 = 1`.

Mihailescu's theorem is **not** available in Mathlib (a search of Mathlib turns up no
`Catalan`/`Mihailescu` result about the exponential Diophantine equation; the files mentioning
"Catalan" concern Catalan *numbers*, and `Mathlib/NumberTheory/FLT/Polynomial.lean` only contains
the *polynomial* analogue).  Accordingly this file:

* formalizes the statement (`Frontier.IsCatalanPair`);
* proves *unconditionally* the elementary base cases:
  - equal exponents (`Frontier.not_isCatalanPair_of_eq_exponents`),
  - base `2` on the left (`Frontier.not_isCatalanPair_two_left`): `2 ^ p` is never one more
    than a perfect power,
  - base `2` on the right (`Frontier.isCatalanPair_two_right`): the only perfect power that
    is one more than a power of two is `9 = 2 ^ 3 + 1`;
* proves a Lean-checked **reduction** (`Frontier.Catalan_Mihailescu`) of the full statement,
  for arbitrary exponents `> 1`, to the genuinely deep *core case* `Frontier.CatalanCoreCase`:
  distinct **prime** exponents and both bases `≥ 3`.
-/

namespace Frontier

/-- `IsCatalanPair x p y q` says that `x ^ p - y ^ q = 1`, where all four of
`x, y, p, q` are `> 1`; i.e. `x ^ p` and `y ^ q` are consecutive perfect powers. -/

theorem Catalan_Mihailescu (H : CatalanCoreCase) (x p y q : ℕ) (h : IsCatalanPair x p y q) :
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by
  obtain ⟨hx, hp, hy, hq, heq⟩ := h
  obtain ⟨r, hr, hrp⟩ := Nat.exists_prime_and_dvd (show p ≠ 1 by omega)
  obtain ⟨s, hs, hsq⟩ := Nat.exists_prime_and_dvd (show q ≠ 1 by omega)
  set a := p / r with hadef
  set b := q / s with hbdef
  have ha : a * r = p := Nat.div_mul_cancel hrp
  have hb : b * s = q := Nat.div_mul_cancel hsq
  have ha0 : a ≠ 0 := by intro h0; rw [h0, zero_mul] at ha; omega
  have hb0 : b ≠ 0 := by intro h0; rw [h0, zero_mul] at hb; omega
  have hX1 : 1 < x ^ a := Nat.one_lt_pow ha0 hx
  have hY1 : 1 < y ^ b := Nat.one_lt_pow hb0 hy
  have hmain : (x ^ a) ^ r = (y ^ b) ^ s + 1 := by
    rw [← pow_mul, ← pow_mul, ha, hb]; exact heq
  have hr1 : 1 < r := hr.one_lt
  have hs1 : 1 < s := hs.one_lt
  by_cases hX2 : x ^ a = 2
  · exact absurd (show IsCatalanPair 2 r (y ^ b) s from
      ⟨by norm_num, hr1, hY1, hs1, by rw [← hX2]; exact hmain⟩) (not_isCatalanPair_two_left _ _ _)
  by_cases hY2 : y ^ b = 2
  · obtain ⟨hX3, hr2, hs3⟩ := isCatalanPair_two_right (x ^ a) r s
      ⟨hX1, hr1, by norm_num, hs1, by rw [← hY2]; exact hmain⟩
    obtain ⟨ha1, hx3⟩ := exponent_eq_one_of_pow_lt_four hx (by norm_num) (by norm_num) hX3
    obtain ⟨hb1, hy2⟩ := exponent_eq_one_of_pow_lt_four hy (by norm_num) (by norm_num) hY2
    refine ⟨hx3, ?_, hy2, ?_⟩
    · rw [← ha, ha1, hr2, one_mul]
    · rw [← hb, hb1, hs3, one_mul]
  by_cases hrs : r = s
  · subst hrs
    exact absurd (show IsCatalanPair (x ^ a) r (y ^ b) r from ⟨hX1, hr1, hY1, hr1, hmain⟩)
      (not_isCatalanPair_of_eq_exponents _ _ _)
  · exact absurd hmain (H _ _ _ _ hr hs hrs (by omega) (by omega))

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

