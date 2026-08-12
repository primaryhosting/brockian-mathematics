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
theorem itself is *not* claimed here; only the reduction is.
-/

namespace Brockian
namespace BetrothedNumbers

open Filter Finset
open scoped Topology

/-! ### Basic definitions -/

/-- The sum-of-divisors function `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

lemma sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = ArithmeticFunction.sigma 1 n := by
  simp [sigmaOne, ArithmeticFunction.sigma_apply]

/-- `m` and `n` form a betrothed (quasi-amicable) pair. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- `n` is a betrothed number: it belongs to some betrothed pair. -/
def IsBetrothed (n : ℕ) : Prop := ∃ m, IsBetrothedPair m n

/-- `n` is the smaller member of some betrothed pair. -/
def IsSmallerBetrothed (n : ℕ) : Prop := ∃ m, IsBetrothedPair n m ∧ n < m

/-- `n` is the larger member of some betrothed pair. -/
def IsLargerBetrothed (n : ℕ) : Prop := ∃ m, IsBetrothedPair m n ∧ m < n

/-- The candidate partner of `n`, namely `σ(n) - n - 1`. -/
def partner (n : ℕ) : ℕ := sigmaOne n - n - 1

/-- Counting function: the number of `1 ≤ n ≤ x` satisfying `P`. -/
noncomputable def countUpTo (P : ℕ → Prop) (x : ℕ) : ℕ := #{n ∈ Finset.Icc 1 x | P n}

/-- A predicate on the naturals has asymptotic density zero. -/
def HasDensityZero (P : ℕ → Prop) : Prop :=
  Tendsto (fun x : ℕ => (countUpTo P x : ℝ) / x) atTop (𝓝 0)

/-! ### Density toolkit -/

lemma countUpTo_eq (P : ℕ → Prop) [DecidablePred P] (x : ℕ) :
    countUpTo P x = #{n ∈ Finset.Icc 1 x | P n} := by
  unfold countUpTo
  congr 1
  exact Finset.filter_congr_decidable _ _ _

lemma countUpTo_le_self (P : ℕ → Prop) (x : ℕ) : countUpTo P x ≤ x := by
  have h := Finset.card_filter_le (Finset.Icc 1 x) P
  simpa [countUpTo, Nat.card_Icc] using h

lemma countUpTo_mono {P Q : ℕ → Prop} (h : ∀ n, P n → Q n) (x : ℕ) :
    countUpTo P x ≤ countUpTo Q x := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, h a ha.2⟩

/-- Splitting a counting function along a disjunction. -/
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
lemma count_multiples_le (d x : ℕ) :
    (countUpTo (fun n => d ∣ n) x : ℝ) ≤ (x : ℝ) / d := by
  rw [countUpTo_eq]
  have hcard : #{n ∈ Finset.Icc 1 x | d ∣ n} = x / d := by
    have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := rfl
    rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  rw [hcard]
  exact Nat.cast_div_le

/-- **Sieve criterion for density zero.**  If, for every `ε > 0`, all sufficiently large
elements of `P` are divisible by some element of a finite set `D` of moduli whose reciprocals
sum to at most `ε`, then `P` has density zero.  This is the standard tool for discarding the
integers with a prescribed small divisor structure. -/
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

lemma sum_inv_sq_le_sub (x : ℕ) (hx : 1 ≤ x) :
    ∑ d ∈ Finset.Icc 1 x, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 - 1 / x := by
  induction x with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hx with h | h
    · simp [← h]
      norm_num
    · have hn : 1 ≤ n := by omega
      have hih := ih hn
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      push_cast
      have key : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / ((n : ℝ) + 1) := by
        rw [div_sub_div _ _ (ne_of_gt hnpos) (ne_of_gt h1),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith

lemma sum_inv_sq_le (x : ℕ) : ∑ d ∈ Finset.Icc 1 x, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · norm_num
  · have h := sum_inv_sq_le_sub x hx
    have : (0 : ℝ) ≤ 1 / x := by positivity
    linarith

/-- `σ(m)/m = ∑_{d ∣ m} 1/d`. -/
lemma sigmaOne_div_self {m : ℕ} (hm : 0 < m) :
    (sigmaOne m : ℝ) / m = ∑ d ∈ m.divisors, (1 : ℝ) / d := by
  have h := Nat.sum_div_divisors (α := ℝ) m (fun d => (1 : ℝ) / d)
  rw [← h, sigmaOne, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hdvd : d ∣ m := (Nat.mem_divisors.1 hd).1
  have hd0 : (d : ℝ) ≠ 0 := by
    have hd0' : d ≠ 0 := by
      rintro rfl
      exact (Nat.mem_divisors.1 hd).2 (zero_dvd_iff.1 hdvd)
    exact_mod_cast hd0'
  rw [Nat.cast_div hdvd hd0]
  field_simp

/-- **Average order bound**: `∑_{m ≤ x} σ(m)/m ≤ 2x`. -/
lemma sum_sigmaOne_div_le (x : ℕ) :
    ∑ m ∈ Finset.Icc 1 x, (sigmaOne m : ℝ) / m ≤ 2 * x := by
  have step1 : ∀ m ∈ Finset.Icc 1 x, (sigmaOne m : ℝ) / m
      = ∑ d ∈ Finset.Icc 1 x, if d ∣ m then (1 : ℝ) / d else 0 := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    rw [sigmaOne_div_self (by omega), ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
        le_trans (Nat.le_of_dvd (by omega) hdvd) hm.2⟩, hdvd⟩
    · rintro ⟨-, hdvd⟩
      exact ⟨hdvd, by omega⟩
  have step2 : ∀ d ∈ Finset.Icc 1 x, (∑ m ∈ Finset.Icc 1 x, if d ∣ m then (1 : ℝ) / d else 0)
      ≤ (x : ℝ) * (1 / (d : ℝ) ^ 2) := by
    intro d hd
    simp only [Finset.mem_Icc] at hd
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : #{m ∈ Finset.Icc 1 x | d ∣ m} = x / d := by
      have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := rfl
      rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
    rw [hcard]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd.1
    have h1 : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / d := Nat.cast_div_le
    have h2 : (x : ℝ) * (1 / (d : ℝ) ^ 2) = ((x : ℝ) / d) * (1 / d) := by field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  calc ∑ m ∈ Finset.Icc 1 x, (sigmaOne m : ℝ) / m
      = ∑ d ∈ Finset.Icc 1 x, ∑ m ∈ Finset.Icc 1 x, if d ∣ m then (1 : ℝ) / d else 0 := by
        rw [Finset.sum_congr rfl step1, Finset.sum_comm]
    _ ≤ ∑ d ∈ Finset.Icc 1 x, (x : ℝ) * (1 / (d : ℝ) ^ 2) := Finset.sum_le_sum step2
    _ = (x : ℝ) * ∑ d ∈ Finset.Icc 1 x, (1 : ℝ) / (d : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (x : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_inv_sq_le x) (by positivity)
    _ = 2 * x := by ring

/-- **Chebyshev-type bound**: integers `m ≤ x` with `σ(m) ≥ K·m` number at most `2x/K`. -/
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
lemma isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

lemma isBetrothed_75 : IsBetrothed 75 := ⟨48, isBetrothedPair_48_75⟩

lemma isSmallerBetrothed_48 : IsSmallerBetrothed 48 :=
  ⟨75, isBetrothedPair_48_75, by norm_num⟩

/-! ### Structure of betrothed pairs -/

lemma partner_eq {m n : ℕ} (h : IsBetrothedPair m n) : partner n = m := by
  have h5 := h.2.2.2.2
  simp only [partner, h5]
  omega

lemma isBetrothedPair_symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h2, h1, h3.symm, by omega, by omega⟩

lemma isBetrothed_iff (n : ℕ) :
    IsBetrothed n ↔ IsSmallerBetrothed n ∨ IsLargerBetrothed n := by
  constructor
  · rintro ⟨m, hpair⟩
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact Or.inr ⟨m, hpair, hlt⟩
    · exact absurd heq hpair.2.2.1
    · exact Or.inl ⟨m, isBetrothedPair_symm hpair, hgt⟩
  · rintro (⟨m, hpair, -⟩ | ⟨m, hpair, -⟩)
    · exact ⟨m, isBetrothedPair_symm hpair⟩
    · exact ⟨m, hpair⟩

/-- The partner map injects the larger members of betrothed pairs into the smaller members. -/
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
lemma count_betrothed_le_two_mul (x : ℕ) :
    countUpTo IsBetrothed x ≤ 2 * countUpTo IsSmallerBetrothed x := by
  have h1 := countUpTo_le_add (fun n hn => (isBetrothed_iff n).1 hn) x
  have h2 := count_larger_le_count_smaller x
  omega

/-- Splitting the smaller members of betrothed pairs according to the ratio of the pair:
either the pair has bounded ratio, or the smaller member is highly abundant. -/
lemma count_smaller_le_add (K x : ℕ) :
    countUpTo IsSmallerBetrothed x ≤
      countUpTo (fun m => ∃ n, IsBetrothedPair m n ∧ m < n ∧ n < K * m) x
        + countUpTo (fun m => K * m ≤ sigmaOne m) x := by
  refine countUpTo_le_add ?_ x
  rintro m ⟨n, hpair, hmn⟩
  by_cases hlt : n < K * m
  · exact Or.inl ⟨n, hpair, hmn, hlt⟩
  · refine Or.inr ?_
    have h4 : sigmaOne m = m + n + 1 := hpair.2.2.2.1
    omega

/-! ### The reduction -/

/-- **Density zero reduction for betrothed numbers.**  If, for every `K`, the smaller members
of betrothed pairs `(m, n)` of bounded ratio `n < K · m` have asymptotic density zero, then the
set of all betrothed numbers has asymptotic density zero.

This is a genuine reduction, not the density theorem itself: the unbounded-ratio part of
Pollack's theorem is proved here unconditionally, from the average order bound
`∑_{m ≤ x} σ(m)/m ≤ 2x`, while the bounded-ratio part remains as the hypothesis `h`. -/
theorem density_zero_reduction
    (h : ∀ K : ℕ, HasDensityZero (fun m => ∃ n, IsBetrothedPair m n ∧ m < n ∧ n < K * m)) :
    HasDensityZero IsBetrothed := by
  rw [hasDensityZero_iff]
  intro ε hε
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℕ, 0 < K ∧ (4 : ℝ) / K ≤ ε / 2 := by
    refine ⟨⌈8 / ε⌉₊ + 1, Nat.succ_pos _, ?_⟩
    have hKpos : (0 : ℝ) < (⌈8 / ε⌉₊ + 1 : ℕ) := by positivity
    have hge : (8 : ℝ) / ε ≤ ((⌈8 / ε⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      have := Nat.le_ceil (8 / ε)
      linarith
    rw [div_le_div_iff₀ hKpos (by norm_num)]
    have h8 : (8 : ℝ) ≤ ε * ((⌈8 / ε⌉₊ + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ hε] at hge
      linarith
    linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  filter_upwards [(hasDensityZero_iff _).1 (h K) (ε / 4) (by positivity),
    eventually_ge_atTop 1] with x hx hx1
  have hxpos : (0 : ℝ) ≤ x := by positivity
  have hb : countUpTo IsBetrothed x ≤ 2 * countUpTo IsSmallerBetrothed x :=
    count_betrothed_le_two_mul x
  have hs := count_smaller_le_add K x
  have hB := count_highly_abundant_le K x hK1
  have hbR : (countUpTo IsBetrothed x : ℝ) ≤
      2 * ((countUpTo (fun m => ∃ n, IsBetrothedPair m n ∧ m < n ∧ n < K * m) x : ℝ)
        + (countUpTo (fun m => K * m ≤ sigmaOne m) x : ℝ)) := by
    have : countUpTo IsBetrothed x ≤
        2 * (countUpTo (fun m => ∃ n, IsBetrothedPair m n ∧ m < n ∧ n < K * m) x
          + countUpTo (fun m => K * m ≤ sigmaOne m) x) := by omega
    exact_mod_cast this
  have hfrac : 4 * (x : ℝ) / K ≤ (ε / 2) * x := by
    have h1 : 4 * (x : ℝ) / K = ((4 : ℝ) / K) * x := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right hK2 hxpos
  have h2K : 2 * (2 * (x : ℝ) / K) = 4 * x / K := by ring
  nlinarith [hx, hB, hbR, hfrac]

end BetrothedNumbers
end Brockian

