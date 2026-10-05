/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 8`.**
`x² - 8·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(so `x ≠ ±1`): namely `(x, y) = (3, 1)`, since `9 - 8 = 1`. -/

theorem pell_8_unbounded (N : ℤ) : ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, N < (n : ℤ) := ⟨N.toNat + 1, by omega⟩
  suffices h : ∀ n : ℕ, ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ 0 < x ∧ (n : ℤ) ≤ y by
    obtain ⟨x, y, h1, _, h3⟩ := h n
    exact ⟨x, y, h1, lt_of_lt_of_le hn h3⟩
  intro n
  induction n with
  | zero => exact ⟨3, 1, by norm_num, by norm_num, by norm_num⟩
  | succ k ih =>
      obtain ⟨x, y, h1, hx, hy⟩ := ih
      have hk : (0:ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
      refine ⟨3 * x + 8 * y, x + 3 * y, pell_8_step h1, by linarith, ?_⟩
      push_cast
      linarith
end Math

