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

theorem counting_betrothed_le (x : ℕ) :
    counting betrothedSet x ≤ 2 * counting lowBetrothedSet x := by
  classical
  have hLF : (Finset.range x).filter (fun n => n ∈ lowBetrothedSet)
      ⊆ (Finset.range x).filter (fun n => n ∈ betrothedSet) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, lowBetrothedSet_subset ha.2⟩
  have hkey : (((Finset.range x).filter (fun n => n ∈ betrothedSet)) \
      ((Finset.range x).filter (fun n => n ∈ lowBetrothedSet))).card
      ≤ ((Finset.range x).filter (fun n => n ∈ lowBetrothedSet)).card := by
    apply Finset.card_le_card_of_injOn partner
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hn ⊢
      obtain ⟨⟨hx, m, hpair⟩, hnot⟩ := hn
      have hnl : ¬ (n < m) := fun hlt =>
        hnot ⟨hx, mem_lowBetrothedSet_iff.mpr ⟨m, hpair, hlt⟩⟩
      have hne : m ≠ n := (hpair.2.2.1).symm
      have hmn : m < n := by omega
      have hpe : partner n = m := partner_eq hpair
      rw [hpe]
      exact ⟨by omega, mem_lowBetrothedSet_iff.mpr ⟨n, isBetrothedPair_symm hpair, hmn⟩⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at ha hb
      rw [← partner_partner ha.1.2, ← partner_partner hb.1.2, hab]
  have hcard := Finset.card_sdiff_add_card_eq_card hLF
  simp only [counting]
  omega

/-- **Density zero reduction for betrothed numbers.**
Pollack's theorem that the betrothed (quasi-amicable) numbers have asymptotic density zero
follows from the corresponding statement for the abundant member of each pair, i.e. for the
purely `σ`-arithmetically defined set `lowBetrothedSet`. -/
