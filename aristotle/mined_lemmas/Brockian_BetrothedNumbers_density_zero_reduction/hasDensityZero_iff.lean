import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Overview

Betrothed (quasi-amicable) numbers are the members of pairs `(m, n)` with `m ≠ n` and
`σ(m) = σ(n) = m + n + 1`.  Pollack proved that the set of betrothed numbers has asymptotic
density zero.  This file decomposes that theorem into reusable pieces and proves everything
except one clearly isolated analytic input, which concerns only pairs of bounded ratio.

Dependency graph (every node is proved in this file, except the node marked `HYP`, which is
the hypothesis of the final reduction theorem):

```
   sum_inv_sq_le                     (∑_{d ≤ x} 1/d² ≤ 2)
        │
        ├──────────────► sum_sigmaOne_div_le      (∑_{m ≤ x} σ(m)/m ≤ 2x)
   sigmaOne_div_self ────►      │
   (σ(m)/m = ∑_{d ∣ m} 1/d)     │
                                ▼
                     count_highly_abundant_le     (#{m ≤ x : σ(m) ≥ K·m} ≤ 2x/K)
                                │
   partner_eq                   │
        │                       │
        ▼                       │
   count_larger_le_count_smaller │        (the partner map is injective)
        │                       │
        ▼                       ▼
   count_betrothed_le_two_mul   count_smaller_le_add
        │                       │
        └───────────┬───────────┘
                    ▼
          density_zero_reduction  ◄── HYP: for every K, the smaller members of betrothed
                                          pairs of bounded ratio (n < K·m) have density 0
```

Also proved here, as independent reusable infrastructure for the remaining bounded-ratio step:
`count_multiples_le` (`#{n ≤ x : d ∣ n} ≤ x/d`) and the sieve criterion
`hasDensityZero_of_covered_by_multiples`.

The remaining hypothesis is strictly weaker than Pollack's theorem: it only concerns betrothed
pairs whose two members have bounded ratio.  The unbounded-ratio part is handled here
unconditionally, via the average order bound `∑_{m ≤ x} σ(m)/m ≤ 2x`.  Accordingly, the density

lemma hasDensityZero_iff (P : ℕ → Prop) :
    HasDensityZero P ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, (countUpTo P x : ℝ) ≤ ε * x := by
  rw [HasDensityZero, Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with x hx hx1
    have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
    have hd := hN x hx
    rw [Real.dist_eq, sub_zero] at hd
    have h2 : (countUpTo P x : ℝ) / x < ε / 2 := lt_of_abs_lt hd
    have h3 := (div_lt_iff₀ hxpos).1 h2
    nlinarith
  · intro h ε hε
    obtain ⟨N, hN⟩ := (h (ε / 2) (half_pos hε)).exists_forall_of_atTop
    refine ⟨max N 1, fun x hx => ?_⟩
    have hx1 : 1 ≤ x := le_trans (le_max_right N 1) hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
    have hle := hN x (le_trans (le_max_left N 1) hx)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hxpos]
    nlinarith

/-- The multiples of `d` up to `x` number at most `x/d`. -/
