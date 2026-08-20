import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

theorem Brun_twin_reciprocal :
    Summable (fun n : ℕ => if n.Prime ∧ (n + 2).Prime then (1 : ℝ) / n else 0) :=
  Brun.summable_twinRecip

end Frontier

import RequestProject.Brun.Bound
import RequestProject.Brun.Mertens

/-!
# An upper bound for the number of twin primes below `N`

Combining the sieve bound with the Mertens-type lower bound, we obtain
`Brun.twin_count_le`: for `j ≥ 16` and any `N`,
`#{n < N : n and n+2 are prime} ≤ 2 N exp (-j) + 2 ^ (E j + 1)`,
where `E j` is an explicit (huge) exponent depending only on `j`.
-/

open Finset

namespace Brun

/-- The odd primes below `W`. -/
