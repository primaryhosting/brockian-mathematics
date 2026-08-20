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

theorem hapSum_eq_sum_Icc (f : ℕ → ℤ) (n d : ℕ) :
    hapSum f n d = ∑ i ∈ Finset.Icc 1 n, f (i * d) := by
  induction n with
  | zero => simp [hapSum]
  | succ n ih =>
      have hlist : hapSum f (n + 1) d = hapSum f n d + f ((n + 1) * d) := by
        simp [hapSum, List.range_succ]
      rw [hlist, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-- **Base case of the Erdős discrepancy problem**, in Mathlib notation: for
every `±1` sequence `f` there are `n, d ≥ 1` with `n * d ≤ 12` such that
`|f d + f (2d) + ⋯ + f (n d)| ≥ 2`. -/
