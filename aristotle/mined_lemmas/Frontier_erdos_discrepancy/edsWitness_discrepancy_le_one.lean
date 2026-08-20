/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no imports): a Lean module docstring
must be the first command in a file, so the required header above forces the
file to contain no `import` lines.  Everything below therefore uses only the
Lean 4 core library.  The file `RequestProject/Main.lean` re-states the results
in Mathlib terms (`∑ i ∈ Finset.Icc 1 n, f (i * d)` and `|·|`) and proves that
the two formulations agree.
-/

namespace Frontier

/-- The partial sum of `f` along the homogeneous arithmetic progression with
common difference `d`, over its first `n` terms:  `f d + f (2d) + ⋯ + f (n d)`. -/

theorem edsWitness_discrepancy_le_one (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hnd : n * d ≤ 11) : (hapSum edsWitness n d).natAbs ≤ 1 := by
  have key : ∀ n < 12, ∀ d < 12, 1 ≤ n → 1 ≤ d → n * d ≤ 11 →
      (hapSum edsWitness n d).natAbs ≤ 1 := by decide
  have hn12 : n < 12 := lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right n hd) hnd) (by norm_num)
  have hd12 : d < 12 := lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_left d hn) hnd) (by norm_num)
  exact key n hn12 d hd12 hn hd hnd

end Frontier

