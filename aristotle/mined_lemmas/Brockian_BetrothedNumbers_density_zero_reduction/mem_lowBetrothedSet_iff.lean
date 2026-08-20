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

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-!
# Betrothed (quasi-amicable) numbers: reduction of Pollack's density-zero theorem

Two distinct positive integers `m ≠ n` are *betrothed* (or *quasi-amicable*) when each is the
sum of the nontrivial proper divisors of the other, i.e. `σ m = σ n = m + n + 1`.
Pollack proved that the set of integers belonging to some betrothed pair has asymptotic
density zero.

This file develops the reusable infrastructure for that theorem and proves the *reduction step*:
the density-zero statement for all betrothed numbers follows from the density-zero statement for
the abundant member of each pair, the latter being described purely `σ`-arithmetically by
`lowBetrothedSet`.

## Dependency graph

```
                       counting_mono ──┐
                                       ├──► hasDensityZero_subset
hasDensityZero_of_counting_le_const_mul┘
                        ▲
                        │
counting_betrothed_le ──┼──────────────────────────► density_zero_reduction
   ▲                    │                                  ▲
   │                    │                                  │
   ├── lowBetrothedSet_subset ◄── mem_lowBetrothedSet_iff   │
   ├── partner_partner ◄── partner_eq, isBetrothedPair_symm │
   └── mem_lowBetrothedSet_iff                              │
                                                            │
        [OPEN ANALYTIC DEPENDENCY: HasDensityZero lowBetrothedSet]
                (Pollack's estimate; supplied as a hypothesis)
```

Everything above the dashed input is proved here unconditionally; the single remaining
analytic input is the density-zero statement for the abundant members, which is the weakest
hypothesis from which the full theorem follows (it is implied by, and here shown to imply,
the full statement).  The density-zero theorem itself is therefore *not* claimed.
-/

namespace Brockian.BetrothedNumbers

/-! ## Counting functions and asymptotic density zero -/

/-- `counting A x` is the number of elements of `A` that are `< x`. -/

theorem mem_lowBetrothedSet_iff {n : ℕ} :
    n ∈ lowBetrothedSet ↔ ∃ m : ℕ, IsBetrothedPair n m ∧ n < m := by
  constructor
  · rintro ⟨hn, habund, hsig⟩
    exact ⟨σ 1 n - n - 1, ⟨hn, by omega, by omega, by omega, by omega⟩, by omega⟩
  · rintro ⟨m, ⟨hn, hm, hne, h1, h2⟩, hlt⟩
    refine ⟨hn, by omega, ?_⟩
    have hm' : σ 1 n - n - 1 = m := by omega
    rw [hm', h2, h1]

/-- The abundant members of betrothed pairs are betrothed numbers. -/
