/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math

/-- The Pell equation `x² - 8·y² = 1` has a nontrivial integer solution
(one with `y ≠ 0`), namely `(x, y) = (3, 1)`, since `3² - 8·1² = 9 - 8 = 1`. -/
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

import Mathlib

/-!
# Pell 8 (Mathlib development)

Supplement to `RequestProject/Math.lean`, which carries the required header comment and
therefore cannot contain an `import` line.  Here we redo the statement over `ℤ` with
Mathlib available, give a proof via Mathlib's Pell machinery (`Pell.pell_eq`), and prove
that the equation `x² - 8·y² = 1` in fact has infinitely many solutions.
-/

set_option autoImplicit false

namespace Math

/-- `x² - 8·y² = 1` has a nontrivial integer solution, stated over `ℤ`.
Proof by the explicit witness `(3, 1)`. -/
theorem pell_8_int : ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 1, by norm_num, one_ne_zero⟩

/-- The same statement over `ℕ`, obtained from Mathlib's Pell machinery:
`Pell.pell_eq` says `xn a1 n * xn a1 n - (a² - 1) * yn a1 n * yn a1 n = 1`,
and for `a = 3` the parameter is `d = 3² - 1 = 8`. -/
theorem pell_8_via_mathlib :
    ∃ x y : ℕ, x * x - 8 * y * y = 1 ∧ y ≠ 0 :=
  ⟨Pell.xn (a := 3) (by decide) 1, Pell.yn (a := 3) (by decide) 1,
    Pell.pell_eq (by decide) 1, by decide⟩

/-- The Brahmagupta/Pell composition step for `d = 8`: from a solution `(x, y)` we get
the new solution `(3x + 8y, x + 3y)`. -/
theorem pell_8_step {x y : ℤ} (h : x ^ 2 - 8 * y ^ 2 = 1) :
    (3 * x + 8 * y) ^ 2 - 8 * (x + 3 * y) ^ 2 = 1 := by
  linear_combination h

/-- There are solutions with `x ≥ 1` and `y` arbitrarily large (natural-number bound). -/
theorem pell_8_exists_ge (n : ℕ) :
    ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ 1 ≤ x ∧ (n : ℤ) ≤ y := by
  induction n with
  | zero => exact ⟨1, 0, by norm_num, by norm_num, by norm_num⟩
  | succ n ih =>
    obtain ⟨x, y, hxy, hx, hy⟩ := ih
    have hy0 : (0 : ℤ) ≤ y := le_trans (by positivity) hy
    refine ⟨3 * x + 8 * y, x + 3 * y, pell_8_step hxy, by linarith, ?_⟩
    push_cast
    linarith

/-- The equation `x² - 8·y² = 1` has infinitely many integer solutions: for every bound `N`
there is a solution with `y > N`. -/
theorem pell_8_infinitely_many (N : ℤ) :
    ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨x, y, hxy, _, hy⟩ := pell_8_exists_ge (N.toNat + 1)
  refine ⟨x, y, hxy, lt_of_lt_of_le ?_ hy⟩
  have : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  push_cast
  linarith

end Math

