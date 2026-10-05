import Mathlib

/-!
# Pell 11 (companion file)

This file complements `RequestProject/Main.lean`, which contains the target theorem
`Math.pell_11` stated over core `Int` (the target file must begin with a fixed header
comment, and in Lean 4 a module docstring cannot precede an `import`, so that file is
Mathlib-free).

Here we restate the result over `ℤ` with Mathlib available, and strengthen it:
the Pell equation `x² - 11 y² = 1` has infinitely many solutions, obtained by iterating
the fundamental solution `(10, 3)`.
-/

namespace Math

/-- Iterating the fundamental solution `(10, 3)` of `x² - 11 y² = 1`:
`(a, b) ↦ (10a + 33b, 3a + 10b)`, starting from the trivial solution `(1, 0)`. -/
def pell11Seq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (10 * (pell11Seq n).1 + 33 * (pell11Seq n).2,
              3 * (pell11Seq n).1 + 10 * (pell11Seq n).2)

/-- Every term of `pell11Seq` solves the Pell equation `x² - 11 y² = 1`. -/
theorem pell11Seq_isSolution (n : ℕ) :
    (pell11Seq n).1 ^ 2 - 11 * (pell11Seq n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pell11Seq]
  | succ n ih =>
      have h : pell11Seq (n + 1) =
          (10 * (pell11Seq n).1 + 33 * (pell11Seq n).2,
           3 * (pell11Seq n).1 + 10 * (pell11Seq n).2) := rfl
      rw [h]
      simp only
      nlinarith [ih]

/-- The terms of `pell11Seq` have first coordinate at least `1` and second coordinate
at least the index; in particular the second coordinates are unbounded. -/
theorem pell11Seq_bounds (n : ℕ) : 1 ≤ (pell11Seq n).1 ∧ (n : ℤ) ≤ (pell11Seq n).2 := by
  induction n with
  | zero => norm_num [pell11Seq]
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      have hb : (0 : ℤ) ≤ (pell11Seq n).2 := le_trans (by positivity) h2
      have h : pell11Seq (n + 1) =
          (10 * (pell11Seq n).1 + 33 * (pell11Seq n).2,
           3 * (pell11Seq n).1 + 10 * (pell11Seq n).2) := rfl
      rw [h]
      constructor
      · simpa using by linarith
      · push_cast
        simpa using by linarith

/-- Strengthening of `Math.pell_11`: the Pell equation `x² - 11 y² = 1` has solutions with
arbitrarily large `y`, hence infinitely many integer solutions. -/
theorem pell_11_unbounded (N : ℤ) : ∃ x y : ℤ, x ^ 2 - 11 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨n, hn⟩ := exists_nat_gt N
  refine ⟨(pell11Seq (n + 1)).1, (pell11Seq (n + 1)).2, pell11Seq_isSolution _, ?_⟩
  have := (pell11Seq_bounds (n + 1)).2
  push_cast at this
  linarith

/-- The Pell equation `x² - 11 y² = 1` has a nontrivial integer solution, stated over `ℤ`. -/
theorem pell_11_int : ∃ x y : ℤ, x ^ 2 - 11 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨10, 3, by norm_num, by norm_num⟩

/-- The set of integer solutions of `x² - 11 y² = 1` is infinite. -/
theorem pell_11_solutions_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 11 * p.2 ^ 2 = 1}.Infinite := by
  have hstep : ∀ n : ℕ, (pell11Seq n).2 < (pell11Seq (n + 1)).2 := by
    intro n
    obtain ⟨h1, h2⟩ := pell11Seq_bounds n
    have hb : (0 : ℤ) ≤ (pell11Seq n).2 := le_trans (by positivity) h2
    have h : pell11Seq (n + 1) =
        (10 * (pell11Seq n).1 + 33 * (pell11Seq n).2,
         3 * (pell11Seq n).1 + 10 * (pell11Seq n).2) := rfl
    rw [h]
    simpa using by linarith
  have hmono : StrictMono fun n : ℕ => (pell11Seq n).2 := strictMono_nat_of_lt_succ hstep
  refine Set.infinite_of_injective_forall_mem (f := pell11Seq) ?_ pell11Seq_isSolution
  intro m n hmn
  exact hmono.injective (congrArg Prod.snd hmn)

end Math

/-!
# Pell 11
Category: Pure Mathematics
Target: Math.pell_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 11·y² = 1` has a nontrivial integer solution,
i.e. a solution with `y ≠ 0`. Witness: `(x, y) = (10, 3)`, since
`10² - 11 · 3² = 100 - 99 = 1`. -/
theorem pell_11 : ∃ x y : Int, x ^ 2 - 11 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨10, 3, by decide, by decide⟩

end Math

