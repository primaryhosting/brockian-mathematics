/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean 4 requires `import` commands to be the very first
commands in a file, and a module docstring `/-! ... -/` counts as a command.
Since the header above must literally begin the file, this module carries no
imports and is developed from the Lean core library only; the statements below
are therefore fully self-contained.  A Mathlib-based companion development
(using `ℤ`, `Set.Infinite`, ...) lives in `RequestProject/PellMathlib.lean`.
-/

namespace Math

/-- The Pell equation `x² - 3·y² = 1` has a nontrivial integer solution,
i.e. a solution with `y ≠ 0` (equivalently `x ≠ ±1`).  Indeed `2² - 3·1² = 1`. -/
theorem pell_3 : ∃ x y : Int, x ^ 2 - 3 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨2, 1, by decide, by decide⟩

/-- The sequence of solutions of `x² - 3·y² = 1` obtained from the fundamental
solution `(2, 1)` by repeatedly applying `(x, y) ↦ (2x + 3y, x + 2y)`
(multiplication by `2 + √3`). -/
def pellSol : Nat → Int × Int
  | 0 => (2, 1)
  | n + 1 => (2 * (pellSol n).1 + 3 * (pellSol n).2, (pellSol n).1 + 2 * (pellSol n).2)

/-- Every term of `pellSol` solves the Pell equation, and its second coordinate
grows at least linearly (in particular the solutions are pairwise distinct). -/
theorem pellSol_spec (n : Nat) :
    (pellSol n).1 ^ 2 - 3 * (pellSol n).2 ^ 2 = 1 ∧
      2 ≤ (pellSol n).1 ∧ (n : Int) + 1 ≤ (pellSol n).2 := by
  induction n with
  | zero => refine ⟨by decide, by decide, by decide⟩
  | succ n ih =>
    obtain ⟨heq, hx, hy⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · show (2 * (pellSol n).1 + 3 * (pellSol n).2) ^ 2
        - 3 * ((pellSol n).1 + 2 * (pellSol n).2) ^ 2 = 1
      grind
    · show 2 ≤ 2 * (pellSol n).1 + 3 * (pellSol n).2
      omega
    · show ((n : Int) + 1) + 1 ≤ (pellSol n).1 + 2 * (pellSol n).2
      have : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
      omega

/-- The Pell equation `x² - 3·y² = 1` has infinitely many integer solutions:
for every bound `N` there is a solution with `y > N`. -/
theorem pell_3_unbounded (N : Int) : ∃ x y : Int, x ^ 2 - 3 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨heq, _, hy⟩ := pellSol_spec N.toNat
  refine ⟨(pellSol N.toNat).1, (pellSol N.toNat).2, heq, ?_⟩
  have hN : N ≤ (N.toNat : Int) := Int.self_le_toNat N
  omega

end Math

import Mathlib
import RequestProject.Main

/-!
# Pell 3 (Mathlib companion)

A Mathlib-based development accompanying `RequestProject/Main.lean`: the Pell
equation `x² - 3·y² = 1` has a nontrivial integer solution, and in fact its
solution set is infinite.
-/

namespace Math

/-- The Pell equation `x² - 3·y² = 1` has a nontrivial integer solution
(one with `y ≠ 0`). -/
theorem pell_3_mathlib : ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨2, 1, by norm_num, by norm_num⟩

/-- The set of integer solutions of `x² - 3·y² = 1` is infinite. -/
theorem pell_3_solutions_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 3 * p.2 ^ 2 = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨⟨a, b⟩, hab⟩
  obtain ⟨x, y, hxy, hy⟩ := Math.pell_3_unbounded b
  have hmem : ((x, y) : ℤ × ℤ) ∈ {p : ℤ × ℤ | p.1 ^ 2 - 3 * p.2 ^ 2 = 1} := hxy
  have hle := (hab hmem).2
  exact absurd hle (by omega)

end Math

