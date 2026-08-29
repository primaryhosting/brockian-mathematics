import Mathlib

/-!
# Pell 8 — companion results

Supplementary development for the target theorem `Math.pell_8`
(`RequestProject/Pell8.lean`): the Pell equation `x² - 8·y² = 1` has not merely one
nontrivial integer solution, but infinitely many, generated from `(3, 1)` by the
automorphism `(x, y) ↦ (3x + 8y, x + 3y)` of the form `x² - 8y²`.
-/

namespace Math

/-- One application of the Pell automorphism attached to the fundamental
solution `(3, 1)` of `x² - 8y² = 1`. -/
def pellStep (p : ℤ × ℤ) : ℤ × ℤ := (3 * p.1 + 8 * p.2, p.1 + 3 * p.2)

/-- The sequence of solutions of `x² - 8y² = 1` obtained by iterating `pellStep`
from the fundamental solution `(3, 1)`. -/
def pellSol : ℕ → ℤ × ℤ
  | 0 => (3, 1)
  | n + 1 => pellStep (pellSol n)

/-- `pellStep` preserves the value of the quadratic form `x² - 8y²`. -/
theorem pellStep_form (p : ℤ × ℤ) :
    (pellStep p).1 ^ 2 - 8 * (pellStep p).2 ^ 2 = p.1 ^ 2 - 8 * p.2 ^ 2 := by
  simp only [pellStep]
  ring

/-- Every term of `pellSol` solves `x² - 8y² = 1`. -/
theorem pellSol_form (n : ℕ) : (pellSol n).1 ^ 2 - 8 * (pellSol n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih => rw [pellSol, pellStep_form, ih]

/-- Both coordinates of `pellSol n` are positive. -/
theorem pellSol_pos (n : ℕ) : 0 < (pellSol n).1 ∧ 0 < (pellSol n).2 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor <;> simp only [pellSol, pellStep] <;> linarith

/-- The `y`-coordinates of `pellSol` grow at least linearly, so they are unbounded. -/
theorem pellSol_snd_ge (n : ℕ) : (n : ℤ) + 1 ≤ (pellSol n).2 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih =>
    have hx : 0 < (pellSol n).1 := (pellSol_pos n).1
    have hy : 0 < (pellSol n).2 := (pellSol_pos n).2
    simp only [pellSol, pellStep]
    push_cast
    linarith

/-- **Infinitely many solutions.** For every bound `N` the Pell equation
`x² - 8·y² = 1` has an integer solution with `y > N`; in particular it has
infinitely many nontrivial integer solutions. -/
theorem pell_8_infinitely_many (N : ℤ) :
    ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ N < y := by
  refine ⟨(pellSol N.toNat).1, (pellSol N.toNat).2, pellSol_form _, ?_⟩
  have h := pellSol_snd_ge N.toNat
  have : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  linarith

/-- The set of nontrivial integer solutions of `x² - 8·y² = 1` is infinite. -/
theorem pell_8_solutions_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 8 * p.2 ^ 2 = 1 ∧ p.2 ≠ 0}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨⟨bx, by'⟩, hb⟩
  obtain ⟨x, y, hxy, hy⟩ := pell_8_infinitely_many (max by' 0)
  have hy0 : y ≠ 0 := by have := le_max_right by' 0; omega
  have hby : by' < y := lt_of_le_of_lt (le_max_left by' 0) hy
  have := hb (show ((x, y) : ℤ × ℤ) ∈ _ from ⟨hxy, hy0⟩)
  exact absurd this.2 (by simpa using hby)

end Math

/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 8·y² = 1` has a nontrivial integer solution
(i.e. one with `y ≠ 0`): take `(x, y) = (3, 1)`. -/
theorem pell_8 : ∃ x y : Int, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 1, by decide, by decide⟩

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

