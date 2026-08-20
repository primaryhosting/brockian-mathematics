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

lemma hasDensityZero_of_covered_by_multiples (P : ℕ → Prop)
    (h : ∀ ε : ℝ, 0 < ε → ∃ (D : Finset ℕ) (N : ℕ), (∀ d ∈ D, 0 < d) ∧
      (∑ d ∈ D, (1 : ℝ) / d ≤ ε) ∧ ∀ n, N ≤ n → P n → ∃ d ∈ D, d ∣ n) :
    HasDensityZero P := by
  rw [hasDensityZero_iff]
  intro ε hε
  obtain ⟨D, N, hDpos, hDsum, hcov⟩ := h (ε / 2) (by positivity)
  have hcount : ∀ x : ℕ, (countUpTo P x : ℝ) ≤ N + (ε / 2) * x := by
    intro x
    have hsub : {n ∈ Finset.Icc 1 x | P n} ⊆
        Finset.Icc 1 N ∪ D.biUnion (fun d => {n ∈ Finset.Icc 1 x | d ∣ n}) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      by_cases hnN : n ≤ N
      · exact Finset.mem_union_left _ (Finset.mem_Icc.2 ⟨hn.1.1, hnN⟩)
      · obtain ⟨d, hdD, hdvd⟩ := hcov n (by omega) hn.2
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2
          ⟨d, hdD, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hn.1, hdvd⟩⟩)
    have hcard : countUpTo P x ≤ N + ∑ d ∈ D, #{n ∈ Finset.Icc 1 x | d ∣ n} := by
      unfold countUpTo
      calc #{n ∈ Finset.Icc 1 x | P n} ≤ _ := Finset.card_le_card hsub
        _ ≤ #(Finset.Icc 1 N) + #(D.biUnion (fun d => {n ∈ Finset.Icc 1 x | d ∣ n})) :=
            Finset.card_union_le _ _
        _ ≤ N + ∑ d ∈ D, #{n ∈ Finset.Icc 1 x | d ∣ n} := by
            gcongr
            · simp [Nat.card_Icc]
            · exact Finset.card_biUnion_le
    have hR : (∑ d ∈ D, (#{n ∈ Finset.Icc 1 x | d ∣ n} : ℝ)) ≤ (ε / 2) * x := by
      have hterm : ∀ d ∈ D, (#{n ∈ Finset.Icc 1 x | d ∣ n} : ℝ) ≤ (x : ℝ) * (1 / d) := by
        intro d hd
        have hmul := count_multiples_le d x
        rw [countUpTo_eq] at hmul
        calc (#{n ∈ Finset.Icc 1 x | d ∣ n} : ℝ) ≤ (x : ℝ) / d := hmul
          _ = (x : ℝ) * (1 / d) := by ring
      calc (∑ d ∈ D, (#{n ∈ Finset.Icc 1 x | d ∣ n} : ℝ)) ≤ ∑ d ∈ D, (x : ℝ) * (1 / d) :=
            Finset.sum_le_sum hterm
        _ = (x : ℝ) * ∑ d ∈ D, (1 : ℝ) / d := by rw [Finset.mul_sum]
        _ ≤ (x : ℝ) * (ε / 2) := mul_le_mul_of_nonneg_left hDsum (by positivity)
        _ = (ε / 2) * x := by ring
    have hcardR := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast at hcardR
    linarith
  have hev : ∀ᶠ x : ℕ in atTop, (N : ℝ) ≤ (ε / 2) * x := by
    obtain ⟨M, hM⟩ := exists_nat_gt ((N : ℝ) / (ε / 2))
    filter_upwards [eventually_ge_atTop M] with x hx
    have hMx : ((M : ℝ)) ≤ x := by exact_mod_cast hx
    have h2 : (N : ℝ) / (ε / 2) ≤ x := le_trans (le_of_lt hM) hMx
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  filter_upwards [hev] with x hx
  have hc := hcount x
  linarith

/-! ### The average order of `σ(n)/n` -/

