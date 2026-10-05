import Mathlib

/-!
# Pell 10 (Mathlib companion)

The main target `Math.pell_10` lives in `RequestProject/Pell10.lean`.  Here we record the
same statement phrased with Mathlib's `ℤ`, together with the stronger fact that the Pell
equation `x² - 10·y² = 1` has infinitely many integer solutions, obtained by iterating the
fundamental solution `(19, 6)`.
-/

namespace Math

/-- Iterating the fundamental solution `(19, 6)` of `x² - 10·y² = 1`:
`(x, y) ↦ (19x + 60y, 6x + 19y)` (multiplication by `19 + 6√10`). -/
def pellSeq : ℕ → ℤ × ℤ
  | 0 => (19, 6)
  | n + 1 => (19 * (pellSeq n).1 + 60 * (pellSeq n).2, 6 * (pellSeq n).1 + 19 * (pellSeq n).2)

lemma pellSeq_sol (n : ℕ) : (pellSeq n).1 ^ 2 - 10 * (pellSeq n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pellSeq]
  | succ n ih =>
    simp only [pellSeq]
    nlinarith [ih]

lemma pellSeq_pos (n : ℕ) : 0 < (pellSeq n).1 ∧ 0 < (pellSeq n).2 := by
  induction n with
  | zero => norm_num [pellSeq]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [pellSeq]
    constructor <;> nlinarith

lemma pellSeq_y_gt (n : ℕ) : (n : ℤ) < (pellSeq n).2 := by
  induction n with
  | zero => norm_num [pellSeq]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := pellSeq_pos n
    simp only [pellSeq]
    push_cast
    nlinarith

/-- The Pell equation `x² - 10·y² = 1` has solutions with arbitrarily large `y`;
in particular it has infinitely many integer solutions. -/
theorem pell_10_infinitely_many (N : ℤ) :
    ∃ x y : ℤ, x ^ 2 - 10 * y ^ 2 = 1 ∧ N < y := by
  refine ⟨(pellSeq N.toNat).1, (pellSeq N.toNat).2, pellSeq_sol _, ?_⟩
  have h := pellSeq_y_gt N.toNat
  have : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  omega

/-- The solution set of `x² - 10·y² = 1` in `ℤ × ℤ` is infinite. -/
theorem pell_10_solutions_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 10 * p.2 ^ 2 = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨⟨a, b⟩, hb⟩
  obtain ⟨x, y, hxy, hy⟩ := pell_10_infinitely_many b
  have := hb (show (x, y) ∈ {p : ℤ × ℤ | p.1 ^ 2 - 10 * p.2 ^ 2 = 1} from hxy)
  exact absurd this.2 (not_le.mpr hy)

end Math

/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 10`.**

The equation `x² - 10·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(equivalently `x ≠ ±1`): indeed `19² - 10·6² = 361 - 360 = 1`.

Note on the file layout: the required header above is a module docstring, which must be the
first command in a Lean file; no `import` may follow it, so this file is written using Lean
core only (`Int` is the same type as Mathlib's `ℤ`).  A Mathlib-based companion file,
`RequestProject/Pell10Mathlib.lean`, additionally shows that the equation has infinitely
many solutions. -/
theorem pell_10 :
    ∃ x y : Int, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 :=
  ⟨19, 6, by decide, by decide, by decide, by decide⟩

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

