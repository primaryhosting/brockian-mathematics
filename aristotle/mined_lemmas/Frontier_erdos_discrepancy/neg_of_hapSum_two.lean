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

theorem neg_of_hapSum_two (f : Nat → Int) (hf : IsPlusMinusOne f) {d : Nat} (hd : 1 ≤ d)
    (h : (hapSum f d 2).natAbs ≤ 1) : f (2 * d) = - f d := by
  have h2 : hapSum f d 2 = f d + f (2 * d) := by simp [hapSum]
  rw [h2] at h
  rcases hf d hd with h1 | h1 <;> rcases hf (2 * d) (by omega) with h3 | h3 <;> omega

/-- **Base case of the Erdős discrepancy problem (`C = 1`), uniform form.**
For every `±1` sequence `f` a homogeneous arithmetic progression witnessing discrepancy
greater than `1` can already be found inside the initial segment `{1, …, 12}`: there are
`d, n ≥ 1` with `n * d ≤ 12` and `|f d + f (2d) + ⋯ + f (nd)| > 1`.

Equivalently: no `±1` sequence of length `12` has discrepancy at most `1` on homogeneous
arithmetic progressions.  (The bound `12` is optimal: there is a `±1` sequence of length
`11` with discrepancy `1`.) -/
