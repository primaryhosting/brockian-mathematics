/-
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- **Pell's equation for `d = 2`.** The equation `x² - 2·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (ruling out the trivial solutions `(±1, 0)`).
Witness: `(x, y) = (3, 2)`, since `9 - 8 = 1`. -/
theorem pell_2 : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 2, by norm_num, by norm_num⟩

/-- `2` is not a square in `ℤ`. -/
theorem not_isSquare_two_int : ¬ IsSquare (2 : ℤ) := by
  rintro ⟨r, hr⟩
  rcases le_or_gt r 1 with h | h
  · rcases le_or_gt (-1) r with h2 | h2
    · interval_cases r <;> omega
    · nlinarith
  · nlinarith

/-- The same statement obtained from Mathlib's general existence theorem for Pell
equations, `Pell.exists_of_not_isSquare` (`Mathlib/NumberTheory/Pell.lean`), which says
that for `0 < d` with `d` not a square there are integers `x, y` with `x² - d·y² = 1`
and `y ≠ 0`. -/
theorem pell_2' : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) not_isSquare_two_int

/-- For every natural number `n` there is a solution of `x² - 2·y² = 1` with `x > 0`
and `y > n`. Solutions are generated from `(3, 2)` by `(x, y) ↦ (3x + 4y, 2x + 3y)`,
i.e. by multiplication by the fundamental unit `3 + 2√2`. -/
theorem pell_2_exists_gt_nat (n : ℕ) :
    ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ 0 < x ∧ (n : ℤ) < y := by
  induction n with
  | zero => exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩
  | succ k ih =>
      obtain ⟨x, y, hxy, hx, hy⟩ := ih
      have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
      refine ⟨3 * x + 4 * y, 2 * x + 3 * y, by ring_nf; linarith [hxy], by linarith, ?_⟩
      push_cast
      linarith

/-- The solutions of `x² - 2·y² = 1` have arbitrarily large `y`. -/
theorem pell_2_exists_gt (N : ℤ) : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨x, y, h1, _, h3⟩ := pell_2_exists_gt_nat N.toNat
  exact ⟨x, y, h1, lt_of_le_of_lt (Int.self_le_toNat N) h3⟩

/-- There are infinitely many integer solutions of `x² - 2·y² = 1`. -/
theorem pell_2_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 2 * p.2 ^ 2 = 1}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := (hfin.image Prod.snd).bddAbove
  obtain ⟨x, y, h1, h2⟩ := pell_2_exists_gt N
  have hy : y ∈ Prod.snd '' {p : ℤ × ℤ | p.1 ^ 2 - 2 * p.2 ^ 2 = 1} := ⟨(x, y), h1, rfl⟩
  exact absurd (hN hy) (by linarith)

end Math

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

