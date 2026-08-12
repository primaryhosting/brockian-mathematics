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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Filter Asymptotics

namespace Brockian
namespace LandauNSquaredPlusOne

/-! ## The statement

Landau's fourth problem asks whether there are infinitely many primes of the form `n ^ 2 + 1`.
This is an open problem, so the main theorem below is a *conditional reduction*: it derives the
conjecture from a Hardy–Littlewood style lower bound for the associated counting function.

Alongside it we prove a number of unconditional results:

* several reformulations of the conjecture (unboundedness of witnesses, unboundedness of the
  counting function, infinitude of the set of primes of the shape `n ^ 2 + 1`);
* the classical congruence restriction on the prime divisors of `n ^ 2 + 1`;
* the unconditional partial result that infinitely many primes divide *some* value `n ^ 2 + 1`.
-/

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime. -/
def LandauSet : Set ℕ := {n : ℕ | Nat.Prime (n ^ 2 + 1)}

/-- The set of primes of the form `n ^ 2 + 1`. -/
def LandauPrimes : Set ℕ := {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 1}

/-- The counting function of Landau's fourth problem: the number of `n < N` with `n ^ 2 + 1`
prime. -/
def landauCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => Nat.Prime (n ^ 2 + 1)).card

/-- A Hardy–Littlewood style lower bound for the counting function of Landau's fourth problem:
for some `c > 0` one has `landauCount N ≥ c * N / log N` for all large `N`.  (The conjectural
asymptotic of Hardy and Littlewood is of exactly this shape, with an explicit constant.) -/
def HardyLittlewoodLowerBound : Prop :=
  ∃ c > 0, ∀ᶠ N : ℕ in atTop, c * (N : ℝ) / Real.log N ≤ (landauCount N : ℝ)

/-! ## Elementary reformulations -/

theorem mem_landauSet_iff (n : ℕ) : n ∈ LandauSet ↔ Nat.Prime (n ^ 2 + 1) := Iff.rfl

/-- Landau's fourth conjecture is equivalent to the existence of arbitrarily large witnesses. -/
theorem landauSet_infinite_iff_forall_exists_gt :
    LandauSet.Infinite ↔ ∀ N : ℕ, ∃ n > N, Nat.Prime (n ^ 2 + 1) := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt, hn⟩
  · intro h
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨N, hN⟩
    obtain ⟨n, hn, hp⟩ := h N
    exact absurd (hN hp) (by omega)

/-- The counting function is monotone. -/
theorem landauCount_mono : Monotone landauCount := by
  intro a b hab
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr hab))

/-- If `n < N` and `n ^ 2 + 1` is prime, then `n` is counted by `landauCount N`. -/
theorem le_landauCount_of_mem {n N : ℕ} (hn : n < N) (hp : Nat.Prime (n ^ 2 + 1)) :
    1 ≤ landauCount N := by
  refine Finset.card_pos.mpr ⟨n, ?_⟩
  simp [Finset.mem_filter, Finset.mem_range, hn, hp]

set_option maxRecDepth 10000 in
/-- A sample value of the counting function: there are exactly `11` numbers `n < 40` with
`n ^ 2 + 1` prime. -/
theorem landauCount_forty : landauCount 40 = 11 := by decide

/-- Landau's fourth conjecture is equivalent to the unboundedness of its counting function. -/
theorem landauSet_infinite_iff_landauCount_unbounded :
    LandauSet.Infinite ↔ ∀ M : ℕ, ∃ N : ℕ, M < landauCount N := by
  constructor
  · intro h M
    obtain ⟨s, hs, hcard⟩ := h.exists_subset_card_eq (M + 1)
    obtain ⟨N, hN⟩ := s.exists_nat_subset_range
    refine ⟨N, ?_⟩
    have hsub : s ⊆ (Finset.range N).filter fun n => Nat.Prime (n ^ 2 + 1) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨hN hx, hs hx⟩
    have := Finset.card_le_card hsub
    simp only [landauCount]
    omega
  · intro h hfin
    obtain ⟨N, hN⟩ := h hfin.toFinset.card
    have hsub : ((Finset.range N).filter fun n => Nat.Prime (n ^ 2 + 1)) ⊆ hfin.toFinset := by
      intro x hx
      exact hfin.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
    have := Finset.card_le_card hsub
    simp only [landauCount] at hN
    omega

/-- Landau's fourth conjecture is equivalent to the infinitude of the set of primes of the
form `n ^ 2 + 1`. -/
theorem landauSet_infinite_iff_landauPrimes_infinite :
    LandauSet.Infinite ↔ LandauPrimes.Infinite := by
  constructor
  · intro h
    have hinj : Set.InjOn (fun n : ℕ => n ^ 2 + 1) LandauSet := by
      intro a _ b _ hab
      have h2 : a ^ 2 = b ^ 2 := by simpa using hab
      nlinarith [sq_nonneg (a + b)]
    refine Set.Infinite.mono (s := (fun n : ℕ => n ^ 2 + 1) '' LandauSet) ?_ (h.image hinj)
    rintro p ⟨n, hn, rfl⟩
    exact ⟨hn, ⟨n, rfl⟩⟩
  · intro h
    rw [landauSet_infinite_iff_forall_exists_gt]
    intro N
    obtain ⟨p, ⟨hp, n, rfl⟩, hlt⟩ := h.exists_gt (N ^ 2 + 1)
    refine ⟨n, ?_, hp⟩
    by_contra hle
    push_neg at hle
    have : n ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hle 2
    omega

/-! ## Prime divisors of `n ^ 2 + 1` -/

/-- Any odd prime divisor of `n ^ 2 + 1` is congruent to `1` modulo `4`. -/
theorem prime_dvd_sq_add_one_mod_four {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ n ^ 2 + 1) : p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq : ((n : ZMod p)) ^ 2 = -1 := by
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    linear_combination h0
  have hne3 : p % 4 ≠ 3 := by
    rw [← ZMod.exists_sq_eq_neg_one_iff]
    exact ⟨(n : ZMod p), by rw [← hsq]; ring⟩
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  omega

/-- Every prime `p ≡ 1 (mod 4)` divides some value `n ^ 2 + 1`. -/
theorem exists_dvd_sq_add_one_of_mod_four_eq_one {p : ℕ} (hp : p.Prime) (h : p % 4 = 1) :
    ∃ n : ℕ, p ∣ n ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  refine ⟨y.val, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, sq, ← hy]
  ring

/-- **Unconditional partial result.** Infinitely many primes divide some value of `n ^ 2 + 1`.
(Landau's fourth problem asks for the much stronger statement that infinitely many of these
values are themselves prime.) -/
theorem infinite_primes_dvd_sq_add_one :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  refine Set.Infinite.mono ?_ (Nat.infinite_setOf_prime_modEq_one (k := 4) (by norm_num))
  rintro p ⟨hp, hmod⟩
  have h : p % 4 = 1 := by simpa [Nat.ModEq] using hmod
  exact ⟨hp, exists_dvd_sq_add_one_of_mod_four_eq_one hp h⟩

/-- **A sieve criterion.**  If `n ≥ 1` and `n ^ 2 + 1` has no prime factor `≤ n`, then `n ^ 2 + 1`
is prime.  (Indeed a composite value would be a product of at least two prime factors, all of
them `> n`, hence would be at least `(n + 1) ^ 2 > n ^ 2 + 1`.) -/
theorem prime_sq_add_one_of_no_small_prime_factor {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n ^ 2 + 1 → n < p) : Nat.Prime (n ^ 2 + 1) := by
  by_contra hnp
  have h1 : 0 < n ^ 2 + 1 := by positivity
  have h2 := Nat.minFac_sq_le_self h1 hnp
  have h3 : (n ^ 2 + 1).minFac.Prime := Nat.minFac_prime (by nlinarith)
  have h4 := h _ h3 (Nat.minFac_dvd _)
  nlinarith

/-- Landau's fourth conjecture is equivalent to the statement that for infinitely many `n` the
number `n ^ 2 + 1` has no prime factor `≤ n`. -/
theorem landauSet_infinite_iff_infinite_no_small_prime_factor :
    LandauSet.Infinite ↔
      {n : ℕ | 1 ≤ n ∧ ∀ p : ℕ, p.Prime → p ∣ n ^ 2 + 1 → n < p}.Infinite := by
  constructor
  · intro h
    refine Set.Infinite.mono ?_ (h.diff (Set.finite_singleton 0))
    rintro n ⟨hn, hn0⟩
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by simpa using hn0)
    refine ⟨hn1, fun p hp hdvd => ?_⟩
    have : p = n ^ 2 + 1 := (Nat.prime_dvd_prime_iff_eq hp hn).mp hdvd
    subst this
    nlinarith
  · intro h
    refine Set.Infinite.mono ?_ h
    rintro n ⟨hn, hp⟩
    exact prime_sq_add_one_of_no_small_prime_factor hn hp

/-! ## The conditional reduction -/

private theorem tendsto_div_log_atTop : Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  refine h0.inv_tendsto_nhdsGT_zero.congr fun x => ?_
  simp [inv_div]

/-- Under a Hardy–Littlewood style lower bound, the counting function is unbounded. -/
theorem landauCount_unbounded_of_hardyLittlewood (H : HardyLittlewoodLowerBound) :
    ∀ M : ℕ, ∃ N : ℕ, M < landauCount N := by
  obtain ⟨c, hc, hH⟩ := H
  intro M
  have hgrow : Tendsto (fun N : ℕ => c * (N : ℝ) / Real.log N) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => c * (x / Real.log x)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc tendsto_div_log_atTop
    have h2 := h1.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    refine h2.congr fun N => ?_
    simp [Function.comp, mul_div_assoc]
  obtain ⟨N, hN1, hN2⟩ := ((hgrow.eventually_ge_atTop ((M : ℝ) + 1)).and hH).exists
  refine ⟨N, ?_⟩
  have hle : (M : ℝ) + 1 ≤ (landauCount N : ℝ) := le_trans hN1 hN2
  have : (M : ℕ) + 1 ≤ landauCount N := by exact_mod_cast hle
  omega

/-- **Landau's fourth conjecture, conditionally.**  Assuming the Hardy–Littlewood style lower
bound `HardyLittlewoodLowerBound` for the counting function of primes of the form `n ^ 2 + 1`,
there are infinitely many natural numbers `n` such that `n ^ 2 + 1` is prime.

Landau's fourth problem is open, so the result is stated as a conditional reduction; the
hypothesis is a quantitative lower bound of the shape predicted by the Hardy–Littlewood
conjecture. -/
theorem LandauFourthConjecture (H : HardyLittlewoodLowerBound) :
    {n : ℕ | Nat.Prime (n ^ 2 + 1)}.Infinite :=
  landauSet_infinite_iff_landauCount_unbounded.mpr
    (landauCount_unbounded_of_hardyLittlewood H)

end LandauNSquaredPlusOne
end Brockian

