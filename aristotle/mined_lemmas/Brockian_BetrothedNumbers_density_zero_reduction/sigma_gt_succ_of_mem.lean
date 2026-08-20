/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Dependency graph

The target `Brockian.BetrothedNumbers.density_zero_reduction` is the *reduction* step of
Pollack's theorem "quasi-amicable (betrothed) numbers are rare": the set of integers belonging
to a betrothed pair has asymptotic density zero.

```
                       density_zero_reduction
                                 |
                                 v
        hasDensityZero_of_counting_le_div          (analytic core, proved here)
                     |                    \
                     v                     v
   tendsto_sqrt_log_atTop (proved)     squeeze / order lemmas (Mathlib)
                     |
                     v
   Real.tendsto_log_atTop, Real.tendsto_sqrt_atTop (Mathlib)
```

Unproved input (the *only* hypothesis, isolated as `PollackBound`):

```
  PollackBound :  #{ n < x : n is betrothed } ≪ x / sqrt (log x)
```

which in turn is where the genuinely hard analytic number theory of Pollack's paper lives
(sieve bounds for `σ(n) = m + n + 1`, normal order of `ω`, Erdős' method for amicable numbers).
Everything else in this file is proved unconditionally:

* `Brockian.BetrothedNumbers.Betrothed`, `betrothedSet`, `counting`, `HasDensityZero` — definitions;
* `counting_mono`, `counting_le`                   — elementary counting bounds;
* `hasDensityZero_mono`                            — density zero passes to subsets;
* `hasDensityZero_iff_isLittleO`                   — reformulation as `N(x) = o(x)`;
* `hasDensityZero_of_counting_le_div`              — the weakest reusable analytic lemma:
    an eventual bound `N(x) ≤ C * x / g x` with `g → ∞` forces density zero;
* `tendsto_sqrt_log_atTop`                         — `√(log x) → ∞` along `ℕ`;
* `Betrothed.symm`, `Betrothed.sigma_eq`, `sigma_gt_succ_of_mem`,
  `not_prime_of_mem`, `one_notMem`, `zero_notMem` — unconditional structure of betrothed numbers;
* `betrothed_48_75`                                — the pair `(48, 75)` is betrothed, so the
    reduction below is not vacuous.

No density statement is claimed unconditionally: `density_zero_reduction` has `PollackBound`
as an explicit hypothesis.
-/

namespace Brockian
namespace BetrothedNumbers

open Filter Asymptotics ArithmeticFunction
open scoped Topology

/-! ## Definitions -/

/-- `Betrothed m n` says that `m` and `n` form a *betrothed* (quasi-amicable) pair:
they are distinct positive integers with `σ(m) = σ(n) = m + n + 1`, i.e. each is the sum of
the *nontrivial* divisors (proper divisors excluding `1`) of the other. -/

theorem sigma_gt_succ_of_mem {n : ℕ} (hn : n ∈ betrothedSet) : n + 1 < sigma 1 n := by
  obtain ⟨m, hm, hn0, hmn, h1, h2⟩ := hn
  omega

