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

lemma count_larger_le_count_smaller (x : ℕ) :
    countUpTo IsLargerBetrothed x ≤ countUpTo IsSmallerBetrothed x := by
  unfold countUpTo
  refine Finset.card_le_card_of_injOn partner ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnx⟩, m, hpair, hmn⟩ := hn
    have hpm : partner n = m := partner_eq hpair
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hpm]; exact hpair.1
    · rw [hpm]; omega
    · exact ⟨n, by rw [hpm]; exact hpair, by rw [hpm]; exact hmn⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    obtain ⟨-, ma, hpa, -⟩ := ha
    obtain ⟨-, mb, hpb, -⟩ := hb
    have h1 : partner a = ma := partner_eq hpa
    have h2 : partner b = mb := partner_eq hpb
    have h3 : partner ma = a := partner_eq (isBetrothedPair_symm hpa)
    have h4 : partner mb = b := partner_eq (isBetrothedPair_symm hpb)
    rw [h1, h2] at hab
    rw [← h3, ← h4, hab]

/-- Every betrothed number is either the smaller member of its pair, or the partner of a
smaller member; hence there are at most twice as many betrothed numbers as smaller members. -/
