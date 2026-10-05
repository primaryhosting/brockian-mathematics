/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is written in plain Lean 4 core (no imports), so that the header comment above
can legally be the very first thing in the file.
-/

namespace Frontier

/-- A `±1` sequence: `f n ∈ {1, -1}` for every index `n ≥ 1`. -/

theorem witness11_discrepancy_one_bounded :
    ∀ d < 12, ∀ n < 12, 1 ≤ d → 1 ≤ n → n * d ≤ 11 →
      (hapSum witness11 d n).natAbs ≤ 1 := by
  decide

/-- **Optimality of the bound `12`.** All partial sums of `witness11` along homogeneous
arithmetic progressions contained in `{1, …, 11}` have absolute value at most `1`; so
there really is a `±1` sequence of length `11` with discrepancy `1`, and the initial
segment `{1, …, 12}` in `Frontier.erdos_discrepancy_uniform` cannot be shortened. -/
