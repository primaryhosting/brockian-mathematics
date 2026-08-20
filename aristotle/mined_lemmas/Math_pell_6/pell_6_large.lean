/-!
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 6·y² = 1` has a nontrivial integer solution, i.e. one
with `y ≠ 0`: take `(x, y) = (5, 2)`, since `5² - 6·2² = 25 - 24 = 1`.

Since the required header comment must be the first thing in this file, the file cannot
carry an `import` line (Lean requires imports to precede any module documentation), so the
statement is phrased with core `Int` multiplication `x * x` in place of `x ^ 2`.  A version
using `^` and stated over `ℤ`, together with the fact that there are infinitely many
solutions, is proved in `RequestProject.Pell6Extra`. -/

theorem pell_6_large (n : ℕ) : ∃ x y : ℤ, x ^ 2 - 6 * y ^ 2 = 1 ∧ 1 ≤ x ∧ (n : ℤ) ≤ y := by
  induction n with
  | zero => exact ⟨1, 0, by norm_num, by norm_num, by norm_num⟩
  | succ n ih =>
    obtain ⟨x, y, hsol, hx, hy⟩ := ih
    refine ⟨5 * x + 12 * y, 2 * x + 5 * y, pell_6_step hsol, by linarith, ?_⟩
    have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    push_cast
    linarith

/-- The solution set of `x² - 6·y² = 1` is infinite. -/
