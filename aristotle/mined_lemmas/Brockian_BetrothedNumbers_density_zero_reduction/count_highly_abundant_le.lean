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

lemma count_highly_abundant_le (K x : ℕ) (hK : 0 < K) :
    (countUpTo (fun m => K * m ≤ sigmaOne m) x : ℝ) ≤ 2 * x / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have main : ∀ T : Finset ℕ, T ⊆ Finset.Icc 1 x → (∀ m ∈ T, K * m ≤ sigmaOne m) →
      (T.card : ℝ) * K ≤ 2 * x := by
    intro T hsub hmem
    refine le_trans ?_ (sum_sigmaOne_div_le x)
    calc (T.card : ℝ) * K = ∑ _m ∈ T, (K : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ T, (sigmaOne m : ℝ) / m := by
          refine Finset.sum_le_sum ?_
          intro m hm
          have hm1 : (0 : ℝ) < m := by
            have hmem' := hsub hm
            rw [Finset.mem_Icc] at hmem'
            exact_mod_cast hmem'.1
          rw [le_div_iff₀ hm1]
          exact_mod_cast hmem m hm
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro i _ _
          positivity
  rw [le_div_iff₀ hKpos, countUpTo_eq]
  exact main _ (Finset.filter_subset _ _) (fun m hm => (Finset.mem_filter.1 hm).2)

/-! ### Non-vacuity: the smallest betrothed pair -/

/-- `(48, 75)` is the smallest betrothed pair: `σ(48) = σ(75) = 124 = 48 + 75 + 1`. -/
