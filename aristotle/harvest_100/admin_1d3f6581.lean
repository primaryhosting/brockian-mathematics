/-
# Pell 5 — Mathlib development
Category: Pure Mathematics
Companion to `Math.pell_5` (see `RequestProject/Main.lean`).
Provenance: Aristotle theorem prover (Harmonic)

This file develops the `d = 5` Pell equation over `ℤ` with Mathlib available:
the existence of a nontrivial solution, and the fact that there are
infinitely many solutions, obtained from the powers of the fundamental
unit `9 + 4√5`.
-/
import Mathlib

namespace Math

/-- The `n`-th solution of `x² - 5y² = 1`, obtained as the coefficients of
`(9 + 4√5)ⁿ`: `pell5Sol 0 = (1, 0)` and
`pell5Sol (n+1) = (9xₙ + 20yₙ, 4xₙ + 9yₙ)`. -/
def pell5Sol : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (9 * (pell5Sol n).1 + 20 * (pell5Sol n).2,
              4 * (pell5Sol n).1 + 9 * (pell5Sol n).2)

/-- Every `pell5Sol n` is a solution of `x² - 5y² = 1`. -/
theorem pell5Sol_isSolution (n : ℕ) :
    (pell5Sol n).1 ^ 2 - 5 * (pell5Sol n).2 ^ 2 = 1 := by
  induction n with
  | zero => simp [pell5Sol]
  | succ n ih =>
    simp only [pell5Sol]
    nlinarith [ih]

/-- The coordinates of `pell5Sol n` grow: `xₙ ≥ 1` and `yₙ ≥ n`. -/
theorem pell5Sol_ge (n : ℕ) : 1 ≤ (pell5Sol n).1 ∧ (n : ℤ) ≤ (pell5Sol n).2 := by
  induction n with
  | zero => simp [pell5Sol]
  | succ n ih =>
    obtain ⟨hx, hy⟩ := ih
    have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    constructor
    · simp only [pell5Sol]
      omega
    · simp only [pell5Sol]
      push_cast
      omega

/-- **Pell's equation for `d = 5` has a nontrivial solution** (Mathlib version):
`x = 9`, `y = 4` works, since `81 - 5 * 16 = 1`. -/
theorem pell_5_int : ∃ x y : ℤ, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨9, 4, by norm_num, by norm_num⟩

/-- **There are infinitely many solutions** of `x² - 5y² = 1`: for every bound `N`
there is a solution with `y > N`. -/
theorem pell_5_infinitely_many (N : ℤ) :
    ∃ x y : ℤ, x ^ 2 - 5 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, N < (n : ℤ) := ⟨(N + 1).toNat, by omega⟩
  refine ⟨(pell5Sol n).1, (pell5Sol n).2, pell5Sol_isSolution n, ?_⟩
  exact lt_of_lt_of_le hn (pell5Sol_ge n).2

/-- The solution set of `x² - 5y² = 1` in `ℤ × ℤ` is infinite. -/
theorem pell_5_solution_set_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 5 * p.2 ^ 2 = 1}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨x, y, hxy, hyN⟩ := pell_5_infinitely_many N.2
  exact absurd (hN (show (x, y) ∈ _ from hxy)).2 (not_le.mpr hyN)

end Math

/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 5`.**
The equation `x² - 5·y² = 1` has a nontrivial integer solution, i.e. a solution
with `y ≠ 0` (equivalently, one other than `(±1, 0)`).  Witness: `x = 9`, `y = 4`,
since `81 - 5 * 16 = 1`. -/
theorem pell_5 : ∃ x y : Int, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨9, 4, by decide, by decide⟩

end Math

