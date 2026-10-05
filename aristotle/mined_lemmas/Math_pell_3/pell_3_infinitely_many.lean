import Mathlib

/-!
# Pell 3 — supplementary results

Beyond the existence of a single nontrivial solution of `x² - 3·y² = 1` (see
`Math.pell_3` in `RequestProject/Main.lean`), we record here that the equation has
arbitrarily large solutions, obtained by iterating the fundamental unit `2 + √3`.
-/

namespace Math

/-- Multiplying a solution of `x² - 3·y² = 1` by the fundamental unit `2 + √3`
gives a new solution with strictly larger `y` (when `x ≥ 1`). -/

theorem pell_3_infinitely_many (N : ℤ) :
    ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ N < y := by
  have key : ∀ n : ℕ, ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ 1 ≤ x ∧ (n : ℤ) ≤ y := by
    intro n
    induction n with
    | zero => exact ⟨1, 0, by ring, by norm_num, by norm_num⟩
    | succ k ih =>
      obtain ⟨x, y, hxy, hx, hy⟩ := ih
      have hy0 : (0 : ℤ) ≤ y := le_trans (by positivity) hy
      refine ⟨2 * x + 3 * y, x + 2 * y, pell_3_step hxy, by linarith, ?_⟩
      push_cast
      linarith
  obtain ⟨x, y, hxy, _, hy⟩ := key (N.toNat + 1)
  have hN : (N : ℤ) ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  refine ⟨x, y, hxy, ?_⟩
  push_cast at hy
  omega

end Math

/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 3·y² = 1` has a nontrivial integer solution, i.e. a solution
with `y ≠ 0` (equivalently, with `x > 1`). Witness: `(x, y) = (2, 1)`. -/
