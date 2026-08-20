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

def primeMask : ℕ :=
  2986793699354964966835927301217008259302263430909374666791341132234264811227334778053757846503498762062113181585587619060298442378116277488631156256376434239092036059285253544964719249140638915200534050206672277004701076777703965152156178915501541779626784833344371752025088121305545633374745450164679680261221317007399539577353874566270292751940695716555300979884638300668247903401038629556206577836

/-- The spokes of the wheel: the primes up to `73`.  Every even `n` with
`4 ≤ n ≤ 1327` has a Goldbach representation whose smaller summand is a spoke. -/
