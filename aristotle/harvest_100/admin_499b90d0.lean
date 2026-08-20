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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ := #{n ∈ Finset.Icc 1 N | n ∈ A}

/-- `A ⊆ ℕ` has asymptotic (natural) density zero. -/
def HasDensityZero (A : Set ℕ) : Prop :=
  Filter.Tendsto (fun N : ℕ => (countUpTo A N : ℝ) / N) Filter.atTop (nhds 0)

/-! ## The sum-of-divisors function and betrothed numbers -/

/-- Sum of divisors, `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `sigmaOne` agrees with Mathlib's arithmetic function `σ 1`. -/
lemma sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply, sigmaOne]

/-- `m` and `n` form a betrothed (quasi-amicable) pair: each is the sum of the
*nontrivial* proper divisors of the other, i.e. `σ(m) = σ(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- The set of betrothed numbers: members of some betrothed pair. -/
def Betrothed : Set ℕ := {n | ∃ m, IsBetrothedPair m n}

/-- Non-vacuity check: `(48, 75)` is a betrothed pair, since `σ(48) = σ(75) = 124`. -/
lemma isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> (rw [sigmaOne]; decide)

/-- Betrothed numbers that are the *smaller* member of their pair. -/
def BetrothedSmall : Set ℕ := {n | ∃ m, IsBetrothedPair m n ∧ n < m}

/-- Betrothed numbers that are the *larger* member of their pair. -/
def BetrothedLarge : Set ℕ := {n | ∃ m, IsBetrothedPair m n ∧ m < n}

/-! ## Generic density-zero toolbox -/

lemma countUpTo_mono {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) : countUpTo A N ≤ countUpTo B N := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at *
  exact ⟨hx.1, h hx.2⟩

lemma countUpTo_union_le (A B : Set ℕ) (N : ℕ) :
    countUpTo (A ∪ B) N ≤ countUpTo A N + countUpTo B N := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at *
  tauto

/-- Comparison test: a set counted by a constant multiple of a density-zero set
has density zero. -/
lemma hasDensityZero_of_countUpTo_le {A B : Set ℕ} (c : ℝ)
    (hB : HasDensityZero B) (h : ∀ N, (countUpTo A N : ℝ) ≤ c * countUpTo B N) :
    HasDensityZero A := by
  have h0 : Filter.Tendsto (fun N : ℕ => c * ((countUpTo B N : ℝ) / N)) Filter.atTop (nhds 0) := by
    simpa using hB.const_mul c
  refine squeeze_zero' ?_ ?_ h0
  · filter_upwards [Filter.eventually_ge_atTop 1] with N _
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    rw [mul_div_assoc']
    have : (0:ℝ) < N := by exact_mod_cast hN
    gcongr
    exact h N

/-- Approximation test: a set that is, up to a set of density `≤ ε`, covered by a
density-zero set for every `ε > 0`, has density zero. -/
lemma hasDensityZero_of_approx {A : Set ℕ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ B : Set ℕ, HasDensityZero B ∧
      ∀ N : ℕ, (countUpTo A N : ℝ) ≤ countUpTo B N + ε * N) :
    HasDensityZero A := by
  unfold HasDensityZero at *
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B, hB, hAB⟩ := h (ε / 4) (by linarith)
  rw [Metric.tendsto_atTop] at hB
  obtain ⟨N₀, hN₀⟩ := hB (ε / 4) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have h1 := hN₀ N (le_trans (le_max_left _ _) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1 ⊢
  have h2 : (countUpTo A N : ℝ) / N ≤ (countUpTo B N : ℝ) / N + ε / 4 := by
    rw [div_add' _ _ _ (ne_of_gt hNpos), div_le_div_iff_of_pos_right hNpos]
    have := hAB N
    linarith
  linarith

/-! ## Analytic input: the average order of `σ(n)/n` -/

private lemma sum_one_div_sq_le_aux (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hnpos : (0:ℝ) < n := by exact_mod_cast hn
      have h1 : (1:ℝ)/((n:ℝ)+1)^2 ≤ 1/n - 1/((n:ℝ)+1) := by
        rw [div_sub_div _ _ (ne_of_gt hnpos) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      linarith

/-- `∑_{d ≤ N} 1/d² ≤ 2`. -/
lemma sum_one_div_sq_le (N : ℕ) : ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · have h2 := sum_one_div_sq_le_aux N h
    have h3 : (0:ℝ) < N := by exact_mod_cast h
    have : (0:ℝ) < 1 / N := by positivity
    linarith

/-- The abundancy `σ(n)/n` is the sum of the reciprocals of the divisors of `n`. -/
lemma sigmaOne_div_eq_sum_inv_divisors {n : ℕ} (hn : 0 < n) :
    (sigmaOne n : ℝ) / n = ∑ d ∈ n.divisors, (1 : ℝ) / d := by
  rw [← Nat.sum_div_divisors n (fun d => (1:ℝ)/d)]
  unfold sigmaOne
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Nat.mem_divisors] at hd
  obtain ⟨hdvd, _⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
  rw [Nat.cast_div_charZero hdvd]
  have : (0:ℝ) < d := by exact_mod_cast hd0
  have : (0:ℝ) < n := by exact_mod_cast hn
  field_simp

/-- The number of multiples of `d` in `[1, N]` is `⌊N/d⌋`. -/
lemma card_multiples_Icc (N d : ℕ) : #{n ∈ Finset.Icc 1 N | d ∣ n} = N / d := by
  rw [← Nat.card_multiples N d]
  refine Finset.card_nbij' (fun n => n - 1) (fun e => e + 1) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc, Finset.mem_range] at *
    obtain ⟨⟨h1, h2⟩, h3⟩ := ha
    refine ⟨by omega, ?_⟩
    rwa [Nat.sub_add_cancel h1]
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc, Finset.mem_range] at *
    exact ⟨⟨by omega, by omega⟩, ha.2⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at ha
    show a - 1 + 1 = a
    omega
  · intro a _
    show a + 1 - 1 = a
    omega

/-- Average order bound: `∑_{n ≤ N} σ(n)/n ≤ 2N`. -/
lemma sum_sigmaOne_div_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (sigmaOne n : ℝ) / n ≤ 2 * N := by
  have step1 : ∑ n ∈ Finset.Icc 1 N, (sigmaOne n : ℝ) / n
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (1:ℝ)/d := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_Icc] at hn
    exact sigmaOne_div_eq_sum_inv_divisors (by omega)
  have step2 : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (1:ℝ)/d
      = ∑ d ∈ Finset.Icc 1 N, ∑ _n ∈ {n ∈ Finset.Icc 1 N | d ∣ n}, (1:ℝ)/d := by
    refine Finset.sum_comm' ?_
    intro n d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdvd, _⟩
      have hdn : d ≤ n := Nat.le_of_dvd (by omega) hdvd
      have : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      exact ⟨⟨⟨h1, h2⟩, hdvd⟩, by omega, by omega⟩
    · rintro ⟨⟨⟨h1, h2⟩, hdvd⟩, _, _⟩
      exact ⟨⟨h1, h2⟩, hdvd, by omega⟩
  rw [step1, step2]
  have step3 : ∀ d ∈ Finset.Icc 1 N, ∑ _n ∈ {n ∈ Finset.Icc 1 N | d ∣ n}, (1:ℝ)/d
      ≤ (N:ℝ) * ((1:ℝ)/(d:ℝ)^2) := by
    intro d hd
    simp only [Finset.mem_Icc] at hd
    rw [Finset.sum_const, card_multiples_Icc, nsmul_eq_mul]
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd.1
    have hle : ((N / d : ℕ) : ℝ) ≤ (N:ℝ)/(d:ℝ) := Nat.cast_div_le
    calc ((N / d : ℕ) : ℝ) * (1/d) ≤ ((N:ℝ)/d) * (1/d) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (N:ℝ) * ((1:ℝ)/(d:ℝ)^2) := by field_simp
  calc ∑ d ∈ Finset.Icc 1 N, ∑ _n ∈ {n ∈ Finset.Icc 1 N | d ∣ n}, (1:ℝ)/d
      ≤ ∑ d ∈ Finset.Icc 1 N, (N:ℝ) * ((1:ℝ)/(d:ℝ)^2) := Finset.sum_le_sum step3
    _ = (N:ℝ) * ∑ d ∈ Finset.Icc 1 N, (1:ℝ)/(d:ℝ)^2 := by rw [Finset.mul_sum]
    _ ≤ (N:ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_one_div_sq_le N) (by positivity)
    _ = 2 * N := by ring

/-- Markov bound: at most `2N/K` integers `n ≤ N` have abundancy `σ(n)/n > K`. -/
lemma countUpTo_abundancy_le {K : ℝ} (hK : 0 < K) (N : ℕ) :
    (countUpTo {n | (K : ℝ) * n < sigmaOne n} N : ℝ) ≤ 2 * N / K := by
  set S : Finset ℕ := {n ∈ Finset.Icc 1 N | n ∈ {n : ℕ | (K : ℝ) * n < sigmaOne n}} with hS
  have hsub : S ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have key : (S.card : ℝ) * K ≤ ∑ n ∈ S, (sigmaOne n : ℝ) / n := by
    have hconst : (S.card : ℝ) * K = ∑ _n ∈ S, K := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [hS, Finset.mem_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn.1.1
    rw [le_div_iff₀ hn0]
    exact le_of_lt hn.2
  have hle : ∑ n ∈ S, (sigmaOne n : ℝ) / n ≤ ∑ n ∈ Finset.Icc 1 N, (sigmaOne n : ℝ) / n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have h2 := sum_sigmaOne_div_le N
  have hfin : (S.card : ℝ) * K ≤ 2 * N := by linarith
  rw [le_div_iff₀ hK]
  simpa [countUpTo, hS] using hfin

/-- Uniform sparsity of the large-abundancy numbers. -/
lemma exists_abundancy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ N : ℕ, (countUpTo {n | (K : ℝ) * n < sigmaOne n} N : ℝ) ≤ ε * N := by
  obtain ⟨K, hK⟩ := exists_nat_ge (2 / ε + 1)
  have hKpos : (0:ℝ) < K := by
    have : (0:ℝ) < 2 / ε + 1 := by positivity
    linarith
  refine ⟨K, fun N => ?_⟩
  refine le_trans (countUpTo_abundancy_le hKpos N) ?_
  rw [div_le_iff₀ hKpos]
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have h2 : 2 / ε ≤ (K:ℝ) := by linarith
  have : 2 ≤ ε * K := by
    rw [div_le_iff₀ hε] at h2
    linarith
  nlinarith

/-! ## Structure of betrothed pairs -/

/-- The partner of a betrothed number is determined by it. -/
lemma partner_eq {m n : ℕ} (h : IsBetrothedPair m n) : m = sigmaOne n - n - 1 := by
  obtain ⟨_, _, _, _, h5⟩ := h
  omega

/-- Betrothed pairs are symmetric. -/
lemma isBetrothedPair_symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h2, h1, Ne.symm h3, by omega, by omega⟩

lemma betrothed_subset_union : Betrothed ⊆ BetrothedSmall ∪ BetrothedLarge := by
  rintro n ⟨m, hm⟩
  rcases lt_trichotomy m n with h | h | h
  · exact Or.inr ⟨m, hm, h⟩
  · exact absurd h hm.2.2.1
  · exact Or.inl ⟨m, hm, h⟩

/-- Pairing each larger member with its (smaller) partner is injective, so the
larger members are at most as numerous as the smaller members. -/
lemma countUpTo_large_le_small (N : ℕ) :
    countUpTo BetrothedLarge N ≤ countUpTo BetrothedSmall N := by
  refine Finset.card_le_card_of_injOn (fun n => sigmaOne n - n - 1) ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, m, hpair, hmn⟩ := hn
    have hm : sigmaOne n - n - 1 = m := (partner_eq hpair).symm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc, hm]
    refine ⟨⟨hpair.1, by omega⟩, n, isBetrothedPair_symm hpair, hmn⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at ha hb
    obtain ⟨_, ma, hpa, _⟩ := ha
    obtain ⟨_, mb, hpb, _⟩ := hb
    have hma : sigmaOne a - a - 1 = ma := (partner_eq hpa).symm
    have hmb : sigmaOne b - b - 1 = mb := (partner_eq hpb).symm
    have hab' : sigmaOne a - a - 1 = sigmaOne b - b - 1 := hab
    rw [hma, hmb] at hab'
    subst hab'
    obtain ⟨_, _, _, ha4, _⟩ := hpa
    obtain ⟨_, _, _, hb4, _⟩ := hpb
    omega

lemma countUpTo_betrothed_le (N : ℕ) :
    (countUpTo Betrothed N : ℝ) ≤ 2 * countUpTo BetrothedSmall N := by
  have h1 : countUpTo Betrothed N ≤ countUpTo (BetrothedSmall ∪ BetrothedLarge) N :=
    countUpTo_mono betrothed_subset_union N
  have h2 := countUpTo_union_le BetrothedSmall BetrothedLarge N
  have h3 := countUpTo_large_le_small N
  have : countUpTo Betrothed N ≤ 2 * countUpTo BetrothedSmall N := by omega
  exact_mod_cast this

/-- Splitting the smaller members by abundancy. -/
lemma betrothedSmall_subset (K : ℕ) :
    BetrothedSmall ⊆ {n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}
      ∪ {n | (K : ℝ) * n < sigmaOne n} := by
  intro n hn
  rcases le_or_gt (sigmaOne n : ℝ) (K * n) with h | h
  · exact Or.inl ⟨hn, h⟩
  · exact Or.inr h

/-- Reduction of the smaller members to the bounded-abundancy core. -/
lemma hasDensityZero_betrothedSmall
    (hcore : ∀ K : ℕ, HasDensityZero {n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}) :
    HasDensityZero BetrothedSmall := by
  refine hasDensityZero_of_approx (fun ε hε => ?_)
  obtain ⟨K, hK⟩ := exists_abundancy_bound ε hε
  refine ⟨{n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}, hcore K, fun N => ?_⟩
  have h1 : countUpTo BetrothedSmall N
      ≤ countUpTo ({n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}
        ∪ {n | (K : ℝ) * n < sigmaOne n}) N := countUpTo_mono (betrothedSmall_subset K) N
  have h2 := countUpTo_union_le {n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}
      {n : ℕ | (K : ℝ) * n < sigmaOne n} N
  have h3 := hK N
  have h4 : (countUpTo BetrothedSmall N : ℝ)
      ≤ (countUpTo {n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n} N : ℝ)
        + (countUpTo {n : ℕ | (K : ℝ) * n < sigmaOne n} N : ℝ) := by
    exact_mod_cast le_trans h1 h2
  linarith

/-! ## Main reduction -/

/-- **Density zero reduction for betrothed numbers.**
Pollack's theorem that the set of betrothed (quasi-amicable) numbers has asymptotic
density zero is reduced here to its analytic core: it suffices to know, for each fixed
bound `K`, that the smaller members of betrothed pairs whose abundancy `σ(n)/n` is at
most `K` form a set of density zero.

The reduction proved here is unconditional and consists of:
* the counting injection from larger to smaller members of betrothed pairs
  (`countUpTo_large_le_small`), so that the whole problem is carried by the smaller
  members;
* the Markov/average-order bound `∑_{n ≤ N} σ(n)/n ≤ 2N` (`sum_sigmaOne_div_le`),
  giving `#{n ≤ N : σ(n) > K n} ≤ 2N/K` (`countUpTo_abundancy_le`), which removes the
  numbers of unbounded abundancy;
* the generic density-zero toolbox (`hasDensityZero_of_approx`,
  `hasDensityZero_of_countUpTo_le`). -/
theorem density_zero_reduction
    (hcore : ∀ K : ℕ, HasDensityZero {n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}) :
    HasDensityZero Betrothed :=
  hasDensityZero_of_countUpTo_le 2 (hasDensityZero_betrothedSmall hcore) countUpTo_betrothed_le

end BetrothedNumbers
end Brockian

