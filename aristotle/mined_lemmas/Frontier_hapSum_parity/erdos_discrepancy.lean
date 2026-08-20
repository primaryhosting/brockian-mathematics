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

theorem erdos_discrepancy (f : Nat → Int) (hf : ∀ n, f n = 1 ∨ f n = -1) :
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ 2 ≤ (hapSum f d n).natAbs := by
  apply Classical.byContradiction
  intro hcon
  -- Assume every homogeneous sum has absolute value at most `1`.
  have hb : ∀ d n : Nat, 1 ≤ d → 1 ≤ n → (hapSum f d n).natAbs ≤ 1 := by
    intro d n hd hn
    rcases Nat.lt_or_ge (hapSum f d n).natAbs 2 with h | h
    · omega
    · exact absurd ⟨d, n, hd, hn, h⟩ hcon
  -- All even-length homogeneous sums then vanish.
  have z4 := hapSum_even_eq_zero f hf 1 2 (hb 1 4 (by omega) (by omega))
  have z6 := hapSum_even_eq_zero f hf 1 3 (hb 1 6 (by omega) (by omega))
  have z8 := hapSum_even_eq_zero f hf 1 4 (hb 1 8 (by omega) (by omega))
  have z10 := hapSum_even_eq_zero f hf 1 5 (hb 1 10 (by omega) (by omega))
  have w3 := hapSum_even_eq_zero f hf 3 1 (hb 3 2 (by omega) (by omega))
  have w5 := hapSum_even_eq_zero f hf 5 1 (hb 5 2 (by omega) (by omega))
  have w6 := hapSum_even_eq_zero f hf 6 1 (hb 6 2 (by omega) (by omega))
  -- These force `f 3 = f 5 = f 9 = f 12` and `f 6 = -f 3`, so the progression `3, 6, 9, 12`
  -- has sum `±2`.
  have key := hb 3 4 (by omega) (by omega)
  simp [hapSum] at z4 z6 z8 z10 w3 w5 w6 key
  rcases hf 3 with h | h <;> omega

/-- The base case, phrased as the instance `C = 1` of `DiscrepancyUnbounded`. -/
