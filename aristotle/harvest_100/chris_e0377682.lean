/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² − 3·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently, other than `(x, y) = (±1, 0)`):
take `(x, y) = (2, 1)`, since `2² − 3·1² = 1`.

(The file has no `import` line because the required header comment must be the very
first thing in the file, and Lean requires `import` commands to precede all other
commands; the proof only uses core `Int` arithmetic, so no import is needed.) -/
theorem pell_3 : ∃ x y : Int, x ^ 2 - 3 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨2, 1, by decide, by decide⟩

end Math

import Mathlib

/-!
# Pell 3 — supplement

A strengthening of `Math.pell_3`: the Pell equation `x² − 3·y² = 1` has infinitely
many integer solutions, obtained by iterating `(x, y) ↦ (2x + 3y, x + 2y)`.
-/

namespace Math

/-- Iterating `(x, y) ↦ (2x + 3y, x + 2y)` starting from `(2, 1)`. -/
def pellStep : Nat → ℤ × ℤ
  | 0 => (2, 1)
  | n + 1 => (2 * (pellStep n).1 + 3 * (pellStep n).2, (pellStep n).1 + 2 * (pellStep n).2)

lemma pellStep_sol (n : Nat) : (pellStep n).1 ^ 2 - 3 * (pellStep n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pellStep]
  | succ n ih => simp only [pellStep]; linear_combination ih

lemma pellStep_pos (n : Nat) : 0 < (pellStep n).1 ∧ 0 < (pellStep n).2 := by
  induction n with
  | zero => norm_num [pellStep]
  | succ n ih => simp only [pellStep]; constructor <;> nlinarith [ih.1, ih.2]

lemma pellStep_snd_lt (n : Nat) : (pellStep n).2 < (pellStep (n + 1)).2 := by
  have := pellStep_pos n
  simp only [pellStep]
  nlinarith [this.1, this.2]

lemma pellStep_snd_ge (n : Nat) : (n : ℤ) ≤ (pellStep n).2 := by
  induction n with
  | zero => simp [pellStep]
  | succ k ih =>
      have := pellStep_snd_lt k
      push_cast
      omega

/-- The equation `x² − 3·y² = 1` has infinitely many integer solutions:
for every bound `N` there is a solution with `y > N`. -/
theorem pell_3_infinitely_many (N : ℤ) : ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨m, hm⟩ := exists_nat_gt N
  exact ⟨(pellStep m).1, (pellStep m).2, pellStep_sol m,
    lt_of_lt_of_le hm (pellStep_snd_ge m)⟩

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

