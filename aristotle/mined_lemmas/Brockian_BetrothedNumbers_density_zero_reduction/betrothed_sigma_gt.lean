import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

open scoped BigOperators
open scoped Classical
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-! ## Betrothed (quasi-amicable) numbers -/

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers whose sums of divisors both equal `n + m + 1`, i.e. each is the sum of the
proper divisors, excluding `1`, of the other. -/

theorem betrothed_sigma_gt {n : ℕ} (hn : n ∈ betrothedSet) : n + 1 < σ 1 n := by
  obtain ⟨m, hn0, hm0, -, h1, -⟩ := hn
  omega

/-! ## The reduction theorem -/

/--
**Density zero reduction for betrothed numbers.**

This is the combinatorial skeleton of Pollack's theorem that the betrothed
(quasi-amicable) numbers have asymptotic density zero, following the Erdős
exceptional-set scheme. The two genuinely analytic inputs are isolated as
hypotheses:

* `hExceptional`: a family `E k` of exceptional sets (in the Erdős/Pollack argument,
  the integers whose factorisation, or whose value of `σ(n)/n`, is atypical at level `k`)
  whose upper density tends to `0` as the level `k` grows;
* `hMain`: for each fixed level `k`, the betrothed numbers *outside* the exceptional set
  `E k` are counted, by the main divisor-sum argument, by at most `x/(k+1)` up to `x`.

From these the theorem concludes that the betrothed numbers have density zero.
No analytic input is assumed beyond the two explicitly stated hypotheses.
-/
