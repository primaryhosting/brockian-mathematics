/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Erdős discrepancy problem concerns the sums of a `±1` sequence along homogeneous
arithmetic progressions `d, 2d, 3d, …`.  For `f : Nat → Int` taking values in `{1, -1}` we write

`hapSum f d n = f d + f (2 * d) + ⋯ + f (n * d)`.

Erdős conjectured, and Tao proved in 2015, that these sums are unbounded: for every `C`
there are `d, n ≥ 1` with `|hapSum f d n| > C`.  That statement is recorded below as the
predicate `Frontier.DiscrepancyUnbounded`.

The theorem proved here, `Frontier.erdos_discrepancy`, is the base case `C = 1`: every `±1`
sequence has discrepancy at least `2` on homogeneous arithmetic progressions.  The proof is a
Lean-checked finite reduction.  Suppose every homogeneous sum had absolute value at most `1`.
A homogeneous sum of `n` terms has the same parity as `n` (`hapSum_parity`), so every
even-length homogeneous sum vanishes (`hapSum_even_eq_zero`).  Applying this to
`d = 1, n = 4, 6, 8, 10` and to `d = 3, 5, 6, n = 2` yields

`f 5 + f 6 = 0`, `f 9 + f 10 = 0`, `f 3 + f 6 = 0`, `f 5 + f 10 = 0`, `f 6 + f 12 = 0`,

whence `f 3 = f 5 = f 9 = f 12` and `f 6 = -f 3`.  Consequently the progression `3, 6, 9, 12`
has sum `f 3 + f 6 + f 9 + f 12 = 2 * f 3 = ±2`, contradicting the assumed bound.

The development is self-contained: it uses only Lean core, no Mathlib.
-/

namespace Frontier

/-- The sum of `f` along the first `n` terms of the homogeneous arithmetic progression with
common difference `d`, i.e. `f d + f (2 * d) + ⋯ + f (n * d)`. -/

theorem hapSum_parity (f : Nat → Int) (hf : ∀ n, f n = 1 ∨ f n = -1) (d n : Nat) :
    (2 : Int) ∣ hapSum f d n - n := by
  induction n with
  | zero => simp [hapSum]
  | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      rcases hf ((k + 1) * d) with h | h <;> simp only [hapSum, h] <;> omega

/-- An even-length homogeneous sum of a `±1` sequence whose absolute value is at most `1`
must be zero. -/
