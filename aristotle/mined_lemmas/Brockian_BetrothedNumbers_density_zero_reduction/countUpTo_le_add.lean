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

lemma countUpTo_le_add {P Q R : ℕ → Prop} (h : ∀ n, P n → Q n ∨ R n) (x : ℕ) :
    countUpTo P x ≤ countUpTo Q x + countUpTo R x := by
  have hsub : {n ∈ Finset.Icc 1 x | P n} ⊆
      {n ∈ Finset.Icc 1 x | Q n} ∪ {n ∈ Finset.Icc 1 x | R n} := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    rcases h a ha.2 with hq | hr
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨ha.1, hq⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ha.1, hr⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

/-- The `ε`-form of having density zero. -/
