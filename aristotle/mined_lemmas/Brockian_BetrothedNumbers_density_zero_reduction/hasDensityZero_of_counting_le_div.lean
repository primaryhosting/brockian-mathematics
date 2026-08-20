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

theorem hasDensityZero_of_counting_le_div {S : Set ℕ} {g : ℕ → ℝ} {C : ℝ} {X : ℕ}
    (hg : Tendsto g atTop atTop)
    (hbound : ∀ x : ℕ, X ≤ x → (counting S x : ℝ) ≤ C * (x : ℝ) / g x) :
    HasDensityZero S := by
  have hgtop : ∀ᶠ x : ℕ in atTop, 1 ≤ g x := hg.eventually_ge_atTop 1
  have hCg : Tendsto (fun x : ℕ => C / g x) atTop (𝓝 0) := by
    simpa using (Filter.Tendsto.div_atTop (f := fun _ : ℕ => C) tendsto_const_nhds hg)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => (0 : ℝ))
    (h := fun x : ℕ => C / g x) tendsto_const_nhds hCg ?_ ?_
  · filter_upwards with x
    positivity
  · filter_upwards [hgtop, Filter.eventually_ge_atTop X, Filter.eventually_ge_atTop 1] with
      x hgx hXx hx1
    have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
    have hgpos : (0 : ℝ) < g x := lt_of_lt_of_le zero_lt_one hgx
    have h := hbound x hXx
    rw [div_le_iff₀ hxpos]
    calc (counting S x : ℝ) ≤ C * (x : ℝ) / g x := h
      _ = C / g x * (x : ℝ) := by field_simp

/-- `√(log x) → ∞` along the naturals. -/
