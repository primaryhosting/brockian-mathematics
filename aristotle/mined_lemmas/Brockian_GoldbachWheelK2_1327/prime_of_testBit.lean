import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command,
-- including module documentation, so the header block above sits just after
-- the single `import Mathlib` line.

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian

/-! ### A kernel-friendly primality test

`Nat.decidablePrime` performs `Θ(n)` trial divisions and is far too slow for
kernel reduction on a few hundred numbers, so we use a small trial-division
test up to `√n` (with fuel) together with a soundness proof. -/

/-- `trialAux n f d` checks that no `e` with `d ≤ e` and `e * e ≤ n` divides `n`,
using `f` units of fuel; it returns `false` when the fuel runs out. -/

theorem prime_of_testBit {n : ℕ} (hn : n < 1328) (h : primeMask.testBit n = true) :
    Nat.Prime n := by
  have := List.all_eq_true.mp primeMask_sound_bool n (List.mem_range.mpr hn)
  simp only [h, Bool.not_true, Bool.false_or] at this
  exact isPrimeB_sound this

/-- The wheel computation: for every even `n = 2 * i + 4` with `i < 662` there is a spoke
`p` with `2 * p ≤ n` such that both `p` and `n - p` are prime (as recorded by `primeMask`). -/
