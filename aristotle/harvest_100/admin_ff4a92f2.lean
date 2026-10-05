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

/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Brockian.BetrothedNumbers.Basic

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Elementary analytic input: numbers of large abundancy are rare

This file proves, unconditionally, the analytic-number-theory ingredients of the
reduction:

* `Brockian.BetrothedNumbers.sum_divisors_swap`: Dirichlet's hyperbola-style
  interchange `∑_{n ≤ x} ∑_{d ∣ n} f d = ∑_{d ≤ x} ⌊x/d⌋ f d`;
* `Brockian.BetrothedNumbers.sum_sigma_div_self_le`: the mean value bound
  `∑_{n ≤ x} σ(n)/n ≤ 2x`;
* `Brockian.BetrothedNumbers.abundant_count_le`: the Markov/Chebyshev bound
  `#{n ≤ x : σ(n) > K n} ≤ 2x/K`;
* `Brockian.BetrothedNumbers.hasDensityZero_of_forall_le`: a convenient
  criterion for asymptotic density zero.
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- The set of integers of abundancy larger than `K`, i.e. `σ(n) > K n`. -/
def abundantSet (K : ℕ) : Set ℕ := {n | 0 < n ∧ K * n < sigma 1 n}

/-- Interchanging the order of summation in a divisor sum:
`∑_{0 < n ≤ x} ∑_{d ∣ n} f d = ∑_{0 < d ≤ x} ⌊x/d⌋ f d`. -/
theorem sum_divisors_swap (x : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Ioc 0 x, ∑ d ∈ n.divisors, f d
      = ∑ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ) * f d := by
  classical
  have step1 : ∀ n ∈ Finset.Ioc 0 x, ∑ d ∈ n.divisors, f d
      = ∑ d ∈ Finset.Ioc 0 x, if d ∣ n then f d else 0 := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨hdvd, hn0⟩
      have := Nat.le_of_dvd hn.1 hdvd
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hn.1, by omega⟩, hdvd⟩
    · rintro ⟨⟨hd0, -⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  exact Nat.Ioc_filter_dvd_card_eq_div x d

/-- The abundancy of `n` is the sum of the reciprocals of its divisors. -/
theorem sigma_div_self (n : ℕ) (hn : 0 < n) :
    (sigma 1 n : ℝ) / n = ∑ d ∈ n.divisors, (1 : ℝ) / d := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [← Nat.sum_div_divisors n (fun d => (1 : ℝ) / d)]
  rw [sigma_one_apply, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Nat.mem_divisors] at hd
  obtain ⟨hdvd, -⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
  have : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
    rw [Nat.cast_div hdvd (by exact_mod_cast hd0.ne')]
  rw [this, one_div_div]

/-- `∑_{0 < d ≤ x} 1/d² ≤ 2 - 1/max x 1`. -/
theorem sum_inv_sq_le (x : ℕ) :
    ∑ d ∈ Finset.Ioc 0 x, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 - 1 / (max x 1 : ℕ) := by
  induction x with
  | zero => norm_num
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      · rw [Finset.sum_Ioc_succ_top (by omega)]
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h1 : ((max n 1 : ℕ) : ℝ) = (n : ℝ) := by simp [Nat.max_eq_left hn]
        have h2 : ((max (n + 1) 1 : ℕ) : ℝ) = ((n : ℝ) + 1) := by simp
        rw [h1] at ih
        rw [h2]
        have key : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
          rw [div_sub_div _ _ (by linarith) (by linarith),
            div_le_div_iff₀ (by positivity) (by positivity)]
          ring_nf
          nlinarith
        push_cast
        linarith

/-- Mean value bound for the abundancy: `∑_{0 < n ≤ x} σ(n)/n ≤ 2x`. -/
theorem sum_sigma_div_self_le (x : ℕ) :
    ∑ n ∈ Finset.Ioc 0 x, (sigma 1 n : ℝ) / n ≤ 2 * x := by
  have h1 : ∑ n ∈ Finset.Ioc 0 x, (sigma 1 n : ℝ) / n
      = ∑ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ) * ((1 : ℝ) / d) := by
    rw [← sum_divisors_swap x (fun d => (1 : ℝ) / d)]
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    exact sigma_div_self n hn.1
  have h2 : ∀ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ) * ((1 : ℝ) / d)
      ≤ (x : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hcast : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := Nat.cast_div_le
    have : ((x / d : ℕ) : ℝ) * ((1 : ℝ) / d) ≤ ((x : ℝ) / d) * ((1 : ℝ) / d) := by
      apply mul_le_mul_of_nonneg_right hcast (by positivity)
    calc ((x / d : ℕ) : ℝ) * ((1 : ℝ) / d) ≤ ((x : ℝ) / d) * ((1 : ℝ) / d) := this
      _ = (x : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) := by field_simp
  calc ∑ n ∈ Finset.Ioc 0 x, (sigma 1 n : ℝ) / n
      = ∑ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ) * ((1 : ℝ) / d) := h1
    _ ≤ ∑ d ∈ Finset.Ioc 0 x, (x : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) := Finset.sum_le_sum h2
    _ = (x : ℝ) * ∑ d ∈ Finset.Ioc 0 x, (1 : ℝ) / (d : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (x : ℝ) * 2 := by
        have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
        have hle : ∑ d ∈ Finset.Ioc 0 x, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 := by
          refine (sum_inv_sq_le x).trans ?_
          have : (0 : ℝ) ≤ 1 / (max x 1 : ℕ) := by positivity
          linarith
        exact mul_le_mul_of_nonneg_left hle hx
    _ = 2 * x := by ring

/-- The counting function of `abundantSet K` as the cardinality of an explicit finset. -/
theorem countUpTo_abundantSet (K x : ℕ) :
    countUpTo (abundantSet K) x
      = #{n ∈ Finset.Ioc 0 x | K * n < sigma 1 n} := by
  classical
  have : abundantSet K ∩ Set.Iic x = ↑({n ∈ Finset.Ioc 0 x | K * n < sigma 1 n}) := by
    ext n
    simp only [abundantSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic,
      Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq]
    tauto
  rw [countUpTo, this, Set.ncard_coe_finset]

/-- **Chebyshev/Markov bound.** The number of `n ≤ x` with `σ(n) > K n` is at most `2x/K`. -/
theorem abundant_count_le (K x : ℕ) (hK : 0 < K) :
    (countUpTo (abundantSet K) x : ℝ) ≤ 2 * x / K := by
  classical
  set F : Finset ℕ := {n ∈ Finset.Ioc 0 x | K * n < sigma 1 n} with hF
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmem : ∀ n ∈ F, (K : ℝ) ≤ (sigma 1 n : ℝ) / n := by
    intro n hn
    simp only [hF, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn0, -⟩, hlt⟩ := hn
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [le_div_iff₀ hn0']
    have : ((K * n : ℕ) : ℝ) ≤ ((sigma 1 n : ℕ) : ℝ) := by exact_mod_cast hlt.le
    push_cast at this
    linarith
  have hcard : (F.card : ℝ) * K ≤ ∑ n ∈ F, (sigma 1 n : ℝ) / n := by
    calc (F.card : ℝ) * K = ∑ _n ∈ F, (K : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ F, (sigma 1 n : ℝ) / n := Finset.sum_le_sum hmem
  have hsub : ∑ n ∈ F, (sigma 1 n : ℝ) / n ≤ ∑ n ∈ Finset.Ioc 0 x, (sigma 1 n : ℝ) / n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro n _ _
    positivity
  have := hcard.trans (hsub.trans (sum_sigma_div_self_le x))
  rw [countUpTo_abundantSet K x, le_div_iff₀ hKR]
  exact this

/-- A criterion for density zero: if the counting function is bounded by `C x` for every
`C > 0` eventually, ... (helper) -/
theorem hasDensityZero_iff (S : Set ℕ) :
    HasDensityZero S ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (countUpTo S x : ℝ) / x < ε := by
  constructor
  · intro h ε hε
    have := (Metric.tendsto_atTop.mp (show Filter.Tendsto _ _ _ from h)) ε hε
    obtain ⟨N, hN⟩ := this
    filter_upwards [Filter.eventually_ge_atTop N] with x hx
    have := hN x hx
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  · intro h
    rw [HasDensityZero, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h ε hε)
    refine ⟨N, fun x hx => ?_⟩
    have hpos : (0 : ℝ) ≤ (countUpTo S x : ℝ) / x := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
    exact hN x hx

end BetrothedNumbers
end Brockian

/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Basic definitions for betrothed (quasi-amicable) numbers

A pair `(m, n)` of positive integers is *betrothed* (or *quasi-amicable*) if
`σ m = σ n = m + n + 1`, i.e. each of the two numbers is the sum of the
non-trivial proper divisors of the other.  This file sets up the basic
definitions, the elementary structure theory of such pairs (in particular the
fact that the partner of a betrothed number is *determined* by the number),
and the notion of asymptotic density zero used in the main reduction theorem.
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- `(m, n)` is a betrothed (quasi-amicable) pair: both are positive and
`σ m = σ n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- `n` is a betrothed number if it belongs to some betrothed pair. -/
def IsBetrothed (n : ℕ) : Prop := ∃ m, IsBetrothedPair m n

/-- The set of betrothed numbers. -/
def betrothedSet : Set ℕ := {n | IsBetrothed n}

/-- The candidate partner of `n`, namely `σ n - n - 1`.  For a betrothed number
this is exactly its (unique) partner. -/
def partner (n : ℕ) : ℕ := sigma 1 n - n - 1

lemma IsBetrothedPair.swap {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, h1, h2⟩ := h
  refine ⟨hn, hm, ?_, ?_⟩ <;> omega

lemma IsBetrothedPair.pos_left {m n : ℕ} (h : IsBetrothedPair m n) : 0 < m := h.1

lemma IsBetrothedPair.pos_right {m n : ℕ} (h : IsBetrothedPair m n) : 0 < n := h.2.1

/-- In a betrothed pair the first entry is recovered from the second. -/
lemma IsBetrothedPair.partner_eq {m n : ℕ} (h : IsBetrothedPair m n) : partner n = m := by
  obtain ⟨-, -, -, h2⟩ := h
  simp only [partner, h2]
  omega

lemma IsBetrothed.pos {n : ℕ} (h : IsBetrothed n) : 0 < n := h.choose_spec.pos_right

lemma IsBetrothed.pair {n : ℕ} (h : IsBetrothed n) : IsBetrothedPair (partner n) n := by
  obtain ⟨m, hm⟩ := h
  rwa [hm.partner_eq]

/-- The partner of a betrothed number is itself betrothed. -/
lemma IsBetrothed.partner_isBetrothed {n : ℕ} (h : IsBetrothed n) : IsBetrothed (partner n) :=
  ⟨n, h.pair.swap⟩

lemma IsBetrothed.partner_pos {n : ℕ} (h : IsBetrothed n) : 0 < partner n := h.pair.pos_left

/-- `partner` is an involution on betrothed numbers; consequently it is injective there. -/
lemma IsBetrothed.partner_partner {n : ℕ} (h : IsBetrothed n) : partner (partner n) = n :=
  h.pair.swap.partner_eq

lemma IsBetrothed.sigma_eq {n : ℕ} (h : IsBetrothed n) :
    sigma 1 n = n + partner n + 1 := by
  have := h.pair.2.2.2
  omega

lemma IsBetrothed.sigma_partner_eq {n : ℕ} (h : IsBetrothed n) :
    sigma 1 (partner n) = n + partner n + 1 := by
  have := h.pair.2.2.1
  omega

/-!
### Counting and density
-/

/-- The number of elements of `S` in `[0, x]`. -/
noncomputable def countUpTo (S : Set ℕ) (x : ℕ) : ℕ := (S ∩ Set.Iic x).ncard

lemma finite_inter_Iic (S : Set ℕ) (x : ℕ) : (S ∩ Set.Iic x).Finite :=
  (Set.finite_Iic x).subset Set.inter_subset_right

/-- A set of naturals has asymptotic density zero. -/
def HasDensityZero (S : Set ℕ) : Prop :=
  Filter.Tendsto (fun x : ℕ => (countUpTo S x : ℝ) / (x : ℝ)) Filter.atTop (nhds 0)

lemma countUpTo_mono {S T : Set ℕ} (h : S ⊆ T) (x : ℕ) : countUpTo S x ≤ countUpTo T x :=
  Set.ncard_le_ncard (Set.inter_subset_inter_left _ h) (finite_inter_Iic T x)

lemma countUpTo_union_le (S T : Set ℕ) (x : ℕ) :
    countUpTo (S ∪ T) x ≤ countUpTo S x + countUpTo T x := by
  have h : (S ∪ T) ∩ Set.Iic x = (S ∩ Set.Iic x) ∪ (T ∩ Set.Iic x) := by
    ext n; simp only [Set.mem_inter_iff, Set.mem_union]; tauto
  simpa [countUpTo, h] using
    Set.ncard_union_le (S ∩ Set.Iic x) (T ∩ Set.Iic x)

end BetrothedNumbers
end Brockian

/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Brockian.BetrothedNumbers.SigmaBounds

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## The reduction

Pollack's theorem states that the set of betrothed (quasi-amicable) numbers has
asymptotic density zero.  This file proves the *reduction step* of that theorem:
the whole statement follows from the "balanced" case, in which the two members
of the pair are within a bounded factor of each other.

Precisely, `density_zero_reduction` shows

  (∀ K ≥ 1, the set of betrothed `n` whose partner `m` satisfies
            `n ≤ K m` and `m ≤ K n` has density zero)
  →  the set of all betrothed numbers has density zero.

The two "unbalanced" regimes are handled *unconditionally* here, using
the elementary analytic bound `abundant_count_le` from `SigmaBounds`:

* if the partner `m` of `n` is much larger than `n` (`m > K n`) then
  `σ n = n + m + 1 > K n`, so `n` has abundancy `> K`, and such `n` have
  counting function at most `2x/K`;
* if the partner `m` is much smaller (`n > K m`) then `σ m = n + m + 1 > K m`,
  so the *partner* has abundancy `> K`, and since `m ≤ x` and `n` is recovered
  from `m` as `σ m - m - 1`, these `n` are also at most `2x/K` in number.
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- Betrothed numbers whose partner is within a factor `K`. -/
def balancedBetrothedSet (K : ℕ) : Set ℕ :=
  {n | ∃ m, IsBetrothedPair m n ∧ n ≤ K * m ∧ m ≤ K * n}

/-- Betrothed numbers that are much larger than their partner. -/
def skewBetrothedSet (K : ℕ) : Set ℕ :=
  {n | IsBetrothed n ∧ K * partner n < n}

/-- Every betrothed number is either of abundancy `> K`, or much larger than its
partner, or balanced. -/
theorem betrothedSet_subset (K : ℕ) :
    betrothedSet ⊆ abundantSet K ∪ skewBetrothedSet K ∪ balancedBetrothedSet K := by
  intro n hn
  have hb : IsBetrothed n := hn
  have hpair := hb.pair
  have hsig : sigma 1 n = n + partner n + 1 := hb.sigma_eq
  rcases lt_or_ge (K * n) (partner n) with hlt | hge
  · exact Or.inl (Or.inl ⟨hb.pos, by omega⟩)
  · rcases lt_or_ge (K * partner n) n with hlt' | hge'
    · exact Or.inl (Or.inr ⟨hb, hlt'⟩)
    · exact Or.inr ⟨partner n, hpair, hge', hge⟩

/-- The skew betrothed numbers `n` (those with `K · partner n < n`) inject, via
`n ↦ partner n`, into the numbers of abundancy `> K` below the same bound. -/
theorem countUpTo_skew_le (K x : ℕ) (hK : 1 ≤ K) :
    countUpTo (skewBetrothedSet K) x ≤ countUpTo (abundantSet K) x := by
  refine Set.ncard_le_ncard_of_injOn partner ?_ ?_ (finite_inter_Iic _ x)
  · rintro n ⟨⟨hb, hlt⟩, hx⟩
    have hple : partner n ≤ K * partner n := Nat.le_mul_of_pos_left _ (by omega)
    have hpn : partner n < n := lt_of_le_of_lt hple hlt
    refine ⟨⟨hb.partner_pos, ?_⟩, ?_⟩
    · have : sigma 1 (partner n) = n + partner n + 1 := hb.sigma_partner_eq
      omega
    · exact le_trans hpn.le hx
  · rintro a ⟨⟨hba, -⟩, -⟩ b ⟨⟨hbb, -⟩, -⟩ hab
    have := hba.partner_partner
    rw [hab, hbb.partner_partner] at this
    exact this.symm

/-- Counting bound: for every `K`, the betrothed numbers up to `x` are at most
`2 · #{n ≤ x : σ n > K n}` plus the balanced betrothed numbers up to `x`. -/
theorem countUpTo_betrothed_le (K x : ℕ) (hK : 1 ≤ K) :
    countUpTo betrothedSet x
      ≤ 2 * countUpTo (abundantSet K) x + countUpTo (balancedBetrothedSet K) x := by
  have h1 : countUpTo betrothedSet x
      ≤ countUpTo (abundantSet K ∪ skewBetrothedSet K) x
        + countUpTo (balancedBetrothedSet K) x :=
    le_trans (countUpTo_mono (betrothedSet_subset K) x)
      (countUpTo_union_le _ _ x)
  have h2 : countUpTo (abundantSet K ∪ skewBetrothedSet K) x
      ≤ countUpTo (abundantSet K) x + countUpTo (skewBetrothedSet K) x :=
    countUpTo_union_le _ _ x
  have h3 := countUpTo_skew_le K x hK
  omega

/-- **Reduction of Pollack's theorem.**  If, for every `K ≥ 1`, the set of betrothed
numbers whose partner lies within a factor `K` has asymptotic density zero, then the
set of *all* betrothed numbers has asymptotic density zero.

The unbalanced regimes are eliminated unconditionally, via the mean-value bound
`∑_{n ≤ x} σ(n)/n ≤ 2x` and the involutivity of the partner map. -/
theorem density_zero_reduction
    (h : ∀ K : ℕ, 1 ≤ K → HasDensityZero (balancedBetrothedSet K)) :
    HasDensityZero betrothedSet := by
  rw [hasDensityZero_iff]
  intro ε hε
  -- choose `K` with `4/K < ε/2`
  obtain ⟨K, hK1, hKε⟩ : ∃ K : ℕ, 1 ≤ K ∧ 4 / (K : ℝ) < ε / 2 := by
    obtain ⟨K, hK⟩ := exists_nat_gt (8 / ε)
    refine ⟨K + 1, by omega, ?_⟩
    have hK0 : (0 : ℝ) < K + 1 := by positivity
    have h8 : 8 / ε < (K : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hK0]
    rw [div_lt_iff₀ hε] at h8
    push_cast
    nlinarith
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK1
  have hbal := (hasDensityZero_iff _).mp (h K hK1) (ε / 2) (by linarith)
  filter_upwards [hbal, Filter.eventually_ge_atTop 1] with x hx hx1
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx1
  have hcount := countUpTo_betrothed_le K x hK1
  have hcountR : (countUpTo betrothedSet x : ℝ)
      ≤ 2 * (countUpTo (abundantSet K) x : ℝ) + (countUpTo (balancedBetrothedSet K) x : ℝ) := by
    exact_mod_cast hcount
  have hab : (countUpTo (abundantSet K) x : ℝ) ≤ 2 * x / K := abundant_count_le K x (by omega)
  have key : (countUpTo betrothedSet x : ℝ) / x
      ≤ 4 / K + (countUpTo (balancedBetrothedSet K) x : ℝ) / x := by
    rw [div_le_iff₀ hxR]
    have : 2 * (countUpTo (abundantSet K) x : ℝ) ≤ 4 * x / K := by
      have : 2 * (2 * (x : ℝ) / K) = 4 * x / K := by ring
      linarith [mul_le_mul_of_nonneg_left hab (by norm_num : (0:ℝ) ≤ 2)]
    have hdiv : (4 / (K : ℝ) + (countUpTo (balancedBetrothedSet K) x : ℝ) / x) * x
        = 4 * x / K + (countUpTo (balancedBetrothedSet K) x : ℝ) := by
      field_simp
    rw [hdiv]
    linarith
  linarith [key, hx]

end BetrothedNumbers
end Brockian

