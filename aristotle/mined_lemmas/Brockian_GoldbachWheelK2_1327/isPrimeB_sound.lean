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

theorem isPrimeB_sound {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  refine Nat.prime_def_le_sqrt.mpr ⟨h.1, fun m hm hms => ?_⟩
  exact trialAux_sound n 40 2 h.2 m hm (Nat.le_sqrt.mp hms)

/-! ### The prime data

`primeMask` is the bitmask of the primes below `1328`: bit `p` is set iff `p` is
prime.  `wheelSpokes` is the set of "spokes" of the Goldbach wheel, i.e. the small
primes that are allowed as the smaller summand. -/

/-- Bitmask of the primes `< 1328`. -/
