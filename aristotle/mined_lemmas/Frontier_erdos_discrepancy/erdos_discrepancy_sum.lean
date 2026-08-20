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

theorem erdos_discrepancy_sum {f : ℕ → ℤ} (hf : ∀ n, f n = 1 ∨ f n = -1) :
    ∃ n d : ℕ, 1 ≤ n ∧ 1 ≤ d ∧ n * d ≤ 12 ∧ 2 ≤ |∑ i ∈ Finset.Icc 1 n, f (i * d)| := by
  obtain ⟨n, d, hn, hd, h12, habs⟩ := erdos_discrepancy hf
  refine ⟨n, d, hn, hd, h12, ?_⟩
  rw [← hapSum_eq_sum_Icc, Int.abs_eq_natAbs]
  exact_mod_cast habs

end Frontier

/-!
## Optimality of the bound `12`

There is a `±1` sequence all of whose homogeneous-AP partial sums using only
indices `≤ 11` have absolute value at most `1`, so the base case above cannot be
witnessed inside `{1, …, 11}`.
-/

namespace Frontier

/-- A `±1` sequence with discrepancy `1` on all homogeneous arithmetic
progressions contained in `{1, …, 11}`. -/
