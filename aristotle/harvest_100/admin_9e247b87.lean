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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ := n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- `usigma n = σ*(n)` is the sum of the unitary divisors of `n`. -/
def usigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is *unitary perfect* if it is positive and `σ*(n) = 2 n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ usigma n = 2 * n

theorem mem_unitaryDivisors {n d : ℕ} (hn : n ≠ 0) :
    d ∈ unitaryDivisors n ↔ ∃ e, n = d * e ∧ Nat.Coprime d e := by
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hc⟩
    exact ⟨n / d, (Nat.mul_div_cancel' hd).symm, hc⟩
  · rintro ⟨e, rfl, hc⟩
    refine ⟨⟨Dvd.intro e rfl, hn⟩, ?_⟩
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp at hn ⊢
    · rwa [Nat.mul_div_cancel_left _ hd]

theorem usigma_one : usigma 1 = 1 := by decide

/-! ## Multiplicativity -/

private theorem eq_of_dvd_of_dvd_of_mul_eq {x y m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hx : x ∣ m) (hy : y ∣ n) (h : x * y = m * n) : x = m ∧ y = n := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hx0 : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have hy0 : 0 < y := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have h2 : x * y * (s * t) = x * y * 1 := by rw [mul_one]; linarith [h]
  have hst : s * t = 1 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
  simp [Nat.eq_one_of_mul_eq_one_right hst, Nat.eq_one_of_mul_eq_one_left hst]

/-- `σ*` is multiplicative: `σ*(m n) = σ*(m) σ*(n)` for coprime positive `m, n`. -/
theorem usigma_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (i := fun p => p.1 * p.2) (j := fun d => (Nat.gcd d m, Nat.gcd d n))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, e⟩ hde
    simp only [Finset.mem_product] at hde
    obtain ⟨d', rfl, hdd⟩ := (mem_unitaryDivisors hm).1 hde.1
    obtain ⟨e', rfl, hee⟩ := (mem_unitaryDivisors hn).1 hde.2
    refine (mem_unitaryDivisors hmn).2 ⟨d' * e', by ring, ?_⟩
    have h1 : Nat.Coprime d e' :=
      (Nat.Coprime.coprime_dvd_left ⟨d', rfl⟩ h).coprime_dvd_right ⟨e, mul_comm _ _⟩
    have h2 : Nat.Coprime e d' :=
      (Nat.Coprime.coprime_dvd_left ⟨e', rfl⟩ h.symm).coprime_dvd_right ⟨d, mul_comm _ _⟩
    exact (Nat.Coprime.mul_right hdd h1).mul_left (Nat.Coprime.mul_right h2 hee)
  · intro d hd
    obtain ⟨f, hf, hdf⟩ := (mem_unitaryDivisors hmn).1 hd
    have hd_eq : Nat.gcd d m * Nat.gcd d n = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr ⟨f, hf⟩
    have hf_eq : Nat.gcd f m * Nat.gcd f n = f :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr ⟨d, by rw [hf]; ring⟩
    have hprod : (Nat.gcd d m * Nat.gcd f m) * (Nat.gcd d n * Nat.gcd f n) = m * n := by
      calc (Nat.gcd d m * Nat.gcd f m) * (Nat.gcd d n * Nat.gcd f n)
          = (Nat.gcd d m * Nat.gcd d n) * (Nat.gcd f m * Nat.gcd f n) := by ring
        _ = m * n := by rw [hd_eq, hf_eq, hf]
    have hcm : Nat.Coprime (Nat.gcd d m) (Nat.gcd f m) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d m)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left f m) hdf)
    have hcn : Nat.Coprime (Nat.gcd d n) (Nat.gcd f n) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d n)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left f n) hdf)
    obtain ⟨hm_eq, hn_eq⟩ := eq_of_dvd_of_dvd_of_mul_eq hm hn
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcm (Nat.gcd_dvd_right d m) (Nat.gcd_dvd_right f m))
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcn (Nat.gcd_dvd_right d n) (Nat.gcd_dvd_right f n))
      hprod
    simp only [Finset.mem_product]
    exact ⟨(mem_unitaryDivisors hm).2 ⟨Nat.gcd f m, hm_eq.symm, hcm⟩,
      (mem_unitaryDivisors hn).2 ⟨Nat.gcd f n, hn_eq.symm, hcn⟩⟩
  · rintro ⟨d, e⟩ hde
    simp only [Finset.mem_product] at hde
    have hdm : d ∣ m := (Nat.mem_divisors.1 (Finset.mem_filter.1 hde.1).1).1
    have hen : e ∣ n := (Nat.mem_divisors.1 (Finset.mem_filter.1 hde.2).1).1
    have h1 : Nat.Coprime e m := Nat.Coprime.coprime_dvd_left hen h.symm
    have h2 : Nat.Coprime d n := Nat.Coprime.coprime_dvd_left hdm h
    simp only [Prod.mk.injEq]
    exact ⟨by rw [Nat.Coprime.gcd_mul_right_cancel d h1, Nat.gcd_eq_left hdm],
      by rw [Nat.Coprime.gcd_mul_left_cancel e h2, Nat.gcd_eq_left hen]⟩
  · intro d hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr
      (Nat.mem_divisors.1 (Finset.mem_filter.1 hd).1).1
  · rintro ⟨d, e⟩ _; rfl

/-- The unitary divisors of a prime power `p ^ k` (`k ≥ 1`) are exactly `1` and `p ^ k`, so
`σ*(p ^ k) = 1 + p ^ k`. -/
theorem usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) : usigma (p ^ k) = 1 + p ^ k := by
  have hp0 : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hne : (1 : ℕ) ≠ p ^ k := by
    have h1 : p ^ 1 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    have := hp.two_le
    simp only [pow_one] at h1
    omega
  have hset : unitaryDivisors (p ^ k) = {1, p ^ k} := by
    ext d
    rw [mem_unitaryDivisors hp0]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨e, he, hc⟩
      obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow hp).1 ⟨e, he⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · left; simp
      · right
        have hee : e = p ^ (k - i) := by
          have h2 : p ^ i * e = p ^ i * p ^ (k - i) := by
            rw [← he, ← pow_add]
            congr 1
            omega
          exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) h2
        subst hee
        have hki : k - i = 0 := by
          by_contra hne0
          have h1 : p ∣ p ^ i := dvd_pow_self p hi.ne'
          have h2 : p ∣ p ^ (k - i) := dvd_pow_self p hne0
          exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hc ▸ Nat.dvd_gcd h1 h2))
        congr 1
        omega
    · rintro (rfl | rfl)
      · exact ⟨p ^ k, by ring, Nat.coprime_one_left _⟩
      · exact ⟨1, by ring, Nat.coprime_one_right _⟩
  rw [usigma, hset, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]

private theorem coprime_list_prod {a : ℕ} :
    ∀ (l : List ℕ), (∀ b ∈ l, Nat.Coprime a b) → Nat.Coprime a l.prod
  | [], _ => by simp
  | b :: l, h => by
      rw [List.prod_cons]
      exact Nat.Coprime.mul_right (h b (by simp))
        (coprime_list_prod l fun c hc => h c (by simp [hc]))

/-- `σ*` of a product of a pairwise coprime list of prime powers is the product of the
`1 + p ^ k`. -/
theorem usigma_list_prod :
    ∀ (l : List ℕ), (∀ x ∈ l, ∃ p k, Nat.Prime p ∧ 0 < k ∧ x = p ^ k) →
      l.Pairwise Nat.Coprime → usigma l.prod = (l.map (fun x => 1 + x)).prod
  | [], _, _ => by simpa using usigma_one
  | a :: l, hpp, hc => by
      obtain ⟨p, k, hp, hk, rfl⟩ := hpp a (by simp)
      have hane : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
      have hlne : l.prod ≠ 0 := by
        refine List.prod_ne_zero ?_
        intro h0
        obtain ⟨q, j, hq, _, hqj⟩ := hpp 0 (by simp [h0])
        exact pow_ne_zero _ hq.pos.ne' hqj.symm
      have hcop : Nat.Coprime (p ^ k) l.prod :=
        coprime_list_prod l fun b hb => (List.pairwise_cons.1 hc).1 b hb
      rw [List.prod_cons, usigma_mul_of_coprime hane hlne hcop, usigma_prime_pow hp hk,
        usigma_list_prod l (fun x hx => hpp x (by simp [hx])) (List.pairwise_cons.1 hc).2]
      simp

/-! ## The five known unitary perfect numbers -/

private theorem usigma_of_list {N : ℕ} {l : List ℕ} (hN : N = l.prod)
    (hpp : ∀ x ∈ l, ∃ p k, Nat.Prime p ∧ 0 < k ∧ x = p ^ k)
    (hc : l.Pairwise Nat.Coprime) : usigma N = (l.map (fun x => 1 + x)).prod := by
  rw [hN, usigma_list_prod l hpp hc]

theorem isUnitaryPerfect_six : IsUnitaryPerfect 6 := by
  refine ⟨by norm_num, ?_⟩
  rw [usigma_of_list (l := [2, 3]) (by norm_num) ?_ ?_]
  · norm_num
  · rintro x hx
    fin_cases hx
    · exact ⟨2, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 1, by norm_num, by norm_num, by norm_num⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil]
    norm_num [Nat.Coprime]

theorem isUnitaryPerfect_sixty : IsUnitaryPerfect 60 := by
  refine ⟨by norm_num, ?_⟩
  rw [usigma_of_list (l := [2 ^ 2, 3, 5]) (by norm_num) ?_ ?_]
  · norm_num
  · rintro x hx
    fin_cases hx
    · exact ⟨2, 2, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 1, by norm_num, by norm_num, by norm_num⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil]
    norm_num [Nat.Coprime]

theorem isUnitaryPerfect_ninety : IsUnitaryPerfect 90 := by
  refine ⟨by norm_num, ?_⟩
  rw [usigma_of_list (l := [2, 3 ^ 2, 5]) (by norm_num) ?_ ?_]
  · norm_num
  · rintro x hx
    fin_cases hx
    · exact ⟨2, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 1, by norm_num, by norm_num, by norm_num⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil]
    norm_num [Nat.Coprime]

theorem isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  refine ⟨by norm_num, ?_⟩
  rw [usigma_of_list (l := [2 ^ 6, 3, 5, 7, 13]) (by norm_num) ?_ ?_]
  · norm_num
  · rintro x hx
    fin_cases hx
    · exact ⟨2, 6, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 1, by norm_num, by norm_num, by norm_num⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil]
    norm_num [Nat.Coprime]

/-- The largest known unitary perfect number,
`2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313`. -/
def largestKnown : ℕ := 146361946186458562560000

theorem isUnitaryPerfect_largestKnown : IsUnitaryPerfect largestKnown := by
  refine ⟨by norm_num [largestKnown], ?_⟩
  rw [usigma_of_list (N := largestKnown)
    (l := [2 ^ 18, 3, 5 ^ 4, 7, 11, 13, 19, 37, 79, 109, 157, 313]) (by norm_num [largestKnown])
    ?_ ?_]
  · norm_num [largestKnown]
  · rintro x hx
    fin_cases hx
    · exact ⟨2, 18, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 4, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨19, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨37, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨79, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨109, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨157, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨313, 1, by norm_num, by norm_num, by norm_num⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil]
    norm_num [Nat.Coprime]

/-! ## The set of known unitary perfect numbers -/

/-- The five known unitary perfect numbers. -/
def knownFive : Finset ℕ := {6, 60, 90, 87360, largestKnown}

theorem card_knownFive : knownFive.card = 5 := by
  simp only [knownFive, largestKnown]
  rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
    Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
    Finset.card_singleton]

theorem isUnitaryPerfect_of_mem_knownFive {m : ℕ} (hm : m ∈ knownFive) : IsUnitaryPerfect m := by
  simp only [knownFive, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact isUnitaryPerfect_six
  · exact isUnitaryPerfect_sixty
  · exact isUnitaryPerfect_ninety
  · exact isUnitaryPerfect_87360
  · exact isUnitaryPerfect_largestKnown

theorem le_largestKnown_of_mem_knownFive {m : ℕ} (hm : m ∈ knownFive) : m ≤ largestKnown := by
  simp only [knownFive, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> norm_num [largestKnown]

/-- Having six unitary perfect numbers is equivalent to the existence of a unitary perfect
number other than the five known ones, i.e. to the genuinely open question. -/
theorem six_unitary_perfect_iff_exists_new :
    (∃ S : Finset ℕ, S.card = 6 ∧ ∀ m ∈ S, IsUnitaryPerfect m) ↔
      ∃ n, IsUnitaryPerfect n ∧ n ∉ knownFive := by
  constructor
  · rintro ⟨S, hcard, hS⟩
    by_contra hcon
    push_neg at hcon
    have hsub : S ⊆ knownFive := fun m hm => hcon m (hS m hm)
    have hle := Finset.card_le_card hsub
    rw [hcard, card_knownFive] at hle
    omega
  · rintro ⟨n, hn, hnot⟩
    refine ⟨insert n knownFive, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hnot, card_knownFive]
    · intro m hm
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact hn
      · exact isUnitaryPerfect_of_mem_knownFive hm

/-! ## Main conditional theorem -/

/--
**Sixth unitary perfect number (conditional reduction).**

Whether a sixth unitary perfect number exists is an open problem: only the five numbers
`6, 60, 90, 87360, 146361946186458562560000` are known, and it is not known whether a further
one exists.

The theorem below is a Lean-checked reduction: *if* there is any unitary perfect number larger
than the largest currently known one, *then* there are at least six unitary perfect numbers,
exhibited as a six-element finite set all of whose members are unitary perfect. The five known
values are verified here from scratch, via the multiplicativity of `σ*`.
-/
theorem SixthUnitaryPerfectExists (n : ℕ) (hn : IsUnitaryPerfect n) (hgt : largestKnown < n) :
    ∃ S : Finset ℕ, S.card = 6 ∧ ∀ m ∈ S, IsUnitaryPerfect m :=
  six_unitary_perfect_iff_exists_new.2
    ⟨n, hn, fun hmem => absurd (le_largestKnown_of_mem_knownFive hmem) (not_le.2 hgt)⟩

end Brockian.UnitaryPerfect

