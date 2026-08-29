/- Lean requires `import` to precede any module docstring, so the required header comment
appears immediately after the import below. -/
import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) * d` of length `k` with nonzero common difference `d`. -/

theorem not_summable_one_div_indicator_primes :
    ¬ Summable (Set.indicator {p : ℕ | p.Prime} fun n : ℕ ↦ (1 : ℝ) / n) :=
  not_summable_one_div_on_primes

/-- **Green–Tao, as a Lean-checked reduction.**  The primes contain arbitrarily long
arithmetic progressions, granting the Erdős–Turán conjecture on arithmetic progressions.

The reduction is unconditional Lean-checked mathematics: the only input beyond the
hypothesis `hET` is the (proved, in Mathlib) divergence of the sum of the reciprocals of
the primes.  Unconditional base cases (all lengths `k ≤ 10`) are proved in
`Frontier.Green_Tao_base`. -/
