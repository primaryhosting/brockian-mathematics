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

theorem wheel_check :
    (List.range 662).all (fun i =>
      wheelSpokes.any (fun p =>
        decide (2 * p ≤ 2 * i + 4) && primeMask.testBit p && primeMask.testBit (2 * i + 4 - p)))
      = true := by decide

/-- **Goldbach wheel, K = 2, modulus 1327.**
Every even number `n` with `4 ≤ n ≤ 1327` is the sum of two primes `p ≤ q`. -/
