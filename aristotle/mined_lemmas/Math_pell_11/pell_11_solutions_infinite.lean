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
