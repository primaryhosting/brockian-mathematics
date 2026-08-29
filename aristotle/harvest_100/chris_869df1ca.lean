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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset Pointwise

/-! ## Basic definitions -/

/-- The sum of the (positive) divisors of `n`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `k` is a sum of *distinct* divisors of `n`. -/
def IsDivisorSum (n k : ℕ) : Prop := ∃ S ⊆ n.divisors, ∑ d ∈ S, d = k

/-- A *practical number*: a positive integer `n` such that every `k ≤ n` is a sum of
distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop := 0 < n ∧ ∀ k ≤ n, IsDivisorSum n k

/-- The convenient strengthening of practicality used throughout: every `k ≤ σ(n)` is a
sum of distinct divisors of `n`.  (This is in fact equivalent to `IsPractical n`, but we
only need one implication.) -/
def Covers (n : ℕ) : Prop := 0 < n ∧ ∀ k ≤ sigma1 n, IsDivisorSum n k

lemma self_le_sigma1 {n : ℕ} (hn : 0 < n) : n ≤ sigma1 n := by
  refine Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) ?_
  simp [Nat.mem_divisors, hn.ne']

lemma Covers.isPractical {n : ℕ} (h : Covers n) : IsPractical n :=
  ⟨h.1, fun k hk => h.2 k (hk.trans (self_le_sigma1 h.1))⟩

lemma sigma1_le_of_dvd {m n : ℕ} (hn : 0 < n) (h : m ∣ n) : sigma1 m ≤ sigma1 n :=
  Finset.sum_le_sum_of_subset (Nat.divisors_subset_of_dvd hn.ne' h)

/-! ## The divisor structure of `n * p ^ j` -/

lemma divisors_mul_prime_pow_succ {n p j : ℕ} (hp : p.Prime) :
    (n * p ^ (j + 1)).divisors = (n.divisors * {p ^ (j + 1)}) ∪ (n * p ^ j).divisors := by
  rw [Nat.divisors_mul, Nat.divisors_mul]
  have h : (p ^ (j + 1)).divisors = {p ^ (j + 1)} ∪ (p ^ j).divisors := by
    rw [Nat.divisors_prime_pow hp, Nat.divisors_prime_pow hp, Finset.range_add_one (n := j + 1)]
    ext x
    simp [Finset.mem_map, Finset.mem_range]
  rw [h, Finset.mul_union]

lemma disjoint_divisors_mul_prime_pow {n p j : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    Disjoint (n.divisors * ({p ^ (j + 1)} : Finset ℕ)) (n * p ^ j).divisors := by
  rw [Finset.disjoint_left]
  rintro x hx hx2
  rw [Finset.mem_mul] at hx
  obtain ⟨d, hd, c, hc, rfl⟩ := hx
  simp only [Finset.mem_singleton] at hc
  subst hc
  rw [Nat.mem_divisors] at hd hx2
  have h1 : p ^ (j + 1) ∣ n * p ^ j := dvd_trans ⟨d, by ring⟩ hx2.1
  rw [pow_succ, mul_comm n (p ^ j)] at h1
  exact hpn ((mul_dvd_mul_iff_left (a := p ^ j) (pow_ne_zero _ hp.pos.ne')).mp h1)

lemma mul_singleton_eq_image (s : Finset ℕ) (c : ℕ) :
    s * ({c} : Finset ℕ) = Finset.image (fun d => d * c) s := by
  ext x; simp [Finset.mem_mul, eq_comm]

lemma sum_mul_singleton {s : Finset ℕ} {c : ℕ} (hc : 0 < c) :
    ∑ d ∈ (s * ({c} : Finset ℕ)), d = c * ∑ d ∈ s, d := by
  rw [mul_singleton_eq_image,
    Finset.sum_image (by intro x _ y _ h; exact Nat.eq_of_mul_eq_mul_right hc h),
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by ring)

lemma sigma1_mul_prime_pow_succ {n p j : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    sigma1 (n * p ^ (j + 1)) = p ^ (j + 1) * sigma1 n + sigma1 (n * p ^ j) := by
  unfold sigma1
  rw [divisors_mul_prime_pow_succ hp,
    Finset.sum_union (disjoint_divisors_mul_prime_pow hp hpn),
    sum_mul_singleton (pow_pos hp.pos _)]

/-! ## The key covering step -/

lemma covers_mul_prime_pow_succ {n p j : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hn : 0 < n)
    (hcov : Covers (n * p ^ j)) (hcovn : Covers n) (hple : p ^ (j + 1) ≤ sigma1 (n * p ^ j) + 1) :
    Covers (n * p ^ (j + 1)) := by
  refine ⟨Nat.mul_pos hn (pow_pos hp.pos _), ?_⟩
  intro k hk
  rw [sigma1_mul_prime_pow_succ hp hpn] at hk
  set c := p ^ (j + 1) with hc
  have hcpos : 0 < c := pow_pos hp.pos _
  set T := sigma1 n with hT
  set t := min T (k / c) with ht
  have htT : t ≤ T := min_le_left _ _
  have hct : c * t ≤ k := by
    calc c * t ≤ c * (k / c) := Nat.mul_le_mul_left _ (min_le_right _ _)
      _ = (k / c) * c := mul_comm _ _
      _ ≤ k := Nat.div_mul_le_self k c
  have hs : k - c * t ≤ sigma1 (n * p ^ j) := by
    rcases le_or_gt T (k / c) with h | h
    · have : t = T := by omega
      rw [this]
      omega
    · have : t = k / c := by omega
      rw [this]
      have hmod : k - c * (k / c) = k % c := by
        have := Nat.div_add_mod k c
        omega
      rw [hmod]
      have : k % c < c := Nat.mod_lt _ hcpos
      omega
  obtain ⟨S₁, hS₁sub, hS₁sum⟩ := hcov.2 (k - c * t) hs
  obtain ⟨S₂, hS₂sub, hS₂sum⟩ := hcovn.2 t htT
  refine ⟨(S₂ * ({c} : Finset ℕ)) ∪ S₁, ?_, ?_⟩
  · rw [divisors_mul_prime_pow_succ hp]
    exact Finset.union_subset_union
      (Finset.mul_subset_mul hS₂sub (Finset.Subset.refl _)) hS₁sub
  · have hdisj : Disjoint (S₂ * ({c} : Finset ℕ)) S₁ :=
      Finset.disjoint_of_subset_left (Finset.mul_subset_mul hS₂sub (Finset.Subset.refl _))
        (Finset.disjoint_of_subset_right hS₁sub (disjoint_divisors_mul_prime_pow hp hpn))
    rw [Finset.sum_union hdisj, sum_mul_singleton hcpos, hS₁sum, hS₂sum]
    omega

lemma sigma1_ge_of_covers_prime {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hn : 0 < n)
    (hple : p ≤ sigma1 n + 1) (j : ℕ) :
    Covers n → Covers (n * p ^ j) ∧ p ^ (j + 1) ≤ sigma1 (n * p ^ j) + 1 := by
  intro hcovn
  induction j with
  | zero => simpa using ⟨hcovn, hple⟩
  | succ j ih =>
    obtain ⟨hcov, hbd⟩ := ih
    refine ⟨covers_mul_prime_pow_succ hp hpn hn hcov hcovn hbd, ?_⟩
    rw [sigma1_mul_prime_pow_succ hp hpn]
    have h1 : p - 1 ≤ sigma1 n := by omega
    have h2 : p ^ (j + 1) * (p - 1) ≤ p ^ (j + 1) * sigma1 n := Nat.mul_le_mul_left _ h1
    have h3 : p ^ (j + 1) * (p - 1) = p ^ (j + 1) * p - p ^ (j + 1) := by
      rw [Nat.mul_sub, mul_one]
    have h5 : p ^ (j + 1 + 1) = p ^ (j + 1) * p := by ring
    rw [h5]
    omega

lemma Covers.mul_prime_pow {n p : ℕ} (hcovn : Covers n) (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hple : p ≤ sigma1 n + 1) (j : ℕ) : Covers (n * p ^ j) :=
  (sigma1_ge_of_covers_prime hp hpn hcovn.1 hple j hcovn).1

/-! ## Multiplying by an arbitrary coprime factor -/

lemma covers_mul_coprime : ∀ m n : ℕ, Covers n → 0 < m → Nat.Coprime m n →
    m ≤ sigma1 n + 1 → Covers (n * m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hcovn hm hcop hle
    by_cases hm1 : m = 1
    · simpa [hm1] using hcovn
    · have hm2 : 2 ≤ m := by omega
      set p := m.minFac with hp'
      have hp : p.Prime := Nat.minFac_prime hm1
      have hpm : p ∣ m := Nat.minFac_dvd m
      set e := m.factorization p with he
      set m' := m / p ^ e with hm'
      have hsplit : p ^ e * m' = m := Nat.ordProj_mul_ordCompl_eq_self m p
      have hpm' : ¬ p ∣ m' := Nat.not_dvd_ordCompl hp (by omega)
      have hepos : 0 < e := hp.factorization_pos_of_dvd (by omega) hpm
      have hm'pos : 0 < m' := Nat.ordCompl_pos p (by omega)
      have hpe2 : 2 ≤ p ^ e := by
        calc 2 ≤ p := hp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos hepos
      have hm'lt : m' < m := by nlinarith
      have hpn : ¬ p ∣ n := by
        intro hdvd
        have : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hdvd
        rw [hcop] at this
        exact hp.ne_one (Nat.dvd_one.mp this)
      have hpsig : p ≤ sigma1 n + 1 := le_trans (Nat.minFac_le (by omega)) hle
      have hcov2 : Covers (n * p ^ e) := hcovn.mul_prime_pow hp hpn hpsig e
      have hdvd : n ∣ n * p ^ e := Dvd.intro _ rfl
      have hsig : sigma1 n ≤ sigma1 (n * p ^ e) :=
        sigma1_le_of_dvd (Nat.mul_pos hcovn.1 (pow_pos hp.pos _)) hdvd
      have hcop' : Nat.Coprime m' (n * p ^ e) := by
        refine Nat.Coprime.mul_right ?_ ?_
        · exact Nat.Coprime.coprime_dvd_left ⟨p ^ e, by rw [← hsplit]; ring⟩ hcop
        · exact Nat.Coprime.pow_right _ (((hp.coprime_iff_not_dvd).mpr hpm').symm)
      have := ih m' hm'lt (n * p ^ e) hcov2 hm'pos hcop' (by omega)
      have heq : n * p ^ e * m' = n * m := by rw [mul_assoc, hsplit]
      rwa [heq] at this

/-! ## Sigma of prime powers times a base -/

lemma sigma1_mul_prime_pow {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (j : ℕ) :
    sigma1 (n * p ^ j) = sigma1 n * ∑ i ∈ Finset.range (j + 1), p ^ i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sigma1_mul_prime_pow_succ hp hpn, ih,
      Finset.sum_range_succ (f := fun i => p ^ i) (n := j + 1)]
    ring

lemma sigma1_one : sigma1 1 = 1 := by decide

lemma sigma1_two : sigma1 2 = 3 := by decide

lemma sigma1_four : sigma1 4 = 7 := by decide

lemma geom_two (k : ℕ) : (∑ i ∈ Finset.range (k + 1), 2 ^ i) + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h : (2 : ℕ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    omega

lemma geom_three (k : ℕ) : 2 * (∑ i ∈ Finset.range (k + 1), 3 ^ i) + 1 = 3 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add]
    have h : (3 : ℕ) ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) := by ring
    omega

lemma geom_seven (k : ℕ) : 6 * (∑ i ∈ Finset.range (k + 1), 7 ^ i) + 1 = 7 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add]
    have h : (7 : ℕ) ^ (k + 1 + 1) = 7 * 7 ^ (k + 1) := by ring
    omega

/-! ## The two families of base numbers -/

lemma covers_one : Covers 1 := by
  refine ⟨one_pos, ?_⟩
  intro k hk
  rw [sigma1_one] at hk
  interval_cases k
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩

lemma covers_two_pow (k : ℕ) : Covers (2 ^ k) := by
  have := covers_one.mul_prime_pow Nat.prime_two (by decide) (by rw [sigma1_one]) k
  rwa [one_mul] at this

lemma sigma1_two_pow (k : ℕ) : sigma1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  have h := sigma1_mul_prime_pow (n := 1) Nat.prime_two (by decide) k
  rw [one_mul, sigma1_one, one_mul] at h
  rw [h, geom_two]

lemma covers_two : Covers 2 := by
  have := covers_two_pow 1
  rwa [pow_one] at this

lemma covers_two_mul_three_pow (a : ℕ) : Covers (2 * 3 ^ a) :=
  covers_two.mul_prime_pow Nat.prime_three (by decide) (by rw [sigma1_two]; omega) a

lemma covers_two_pow_mul_seven_pow {k : ℕ} (hk : 2 ≤ k) (d : ℕ) : Covers (2 ^ k * 7 ^ d) := by
  refine (covers_two_pow k).mul_prime_pow (by norm_num) ?_ ?_ d
  · intro h
    have := Nat.Prime.dvd_of_dvd_pow (p := 7) (by norm_num) h
    norm_num at this
  · have h := sigma1_two_pow k
    have : (2 : ℕ) ^ 3 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

lemma sigma1_two_mul_three_pow_ge {a : ℕ} (ha : 1 ≤ a) : 4 * 3 ^ a ≤ sigma1 (2 * 3 ^ a) := by
  have h := sigma1_mul_prime_pow (n := 2) Nat.prime_three (by decide) a
  rw [sigma1_two] at h
  have hg := geom_three a
  have h3 : (3 : ℕ) ^ (a + 1) = 3 * 3 ^ a := by ring
  have h1 : (3 : ℕ) ≤ 3 ^ a := by
    calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  omega

lemma sigma1_four_mul_seven_pow_ge {b : ℕ} (hb : 1 ≤ b) : 8 * 7 ^ b ≤ sigma1 (4 * 7 ^ b) := by
  have h := sigma1_mul_prime_pow (n := 4) (p := 7) (by norm_num) (by decide) b
  rw [sigma1_four] at h
  have hg := geom_seven b
  have h7 : (7 : ℕ) ^ (b + 1) = 7 * 7 ^ b := by ring
  have h1 : (7 : ℕ) ≤ 7 ^ b := by
    calc (7 : ℕ) = 7 ^ 1 := (pow_one 7).symm
      _ ≤ 7 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  omega

/-! ## Practicality of the two shapes -/

lemma covers_two_mul_three_pow_mul {a m : ℕ} (ha : 1 ≤ a) (hm : 0 < m) (hodd : ¬ 2 ∣ m)
    (hle : m ≤ 4 * 3 ^ a) : Covers (2 * 3 ^ a * m) := by
  set c := m.factorization 3 with hc
  set m₃ := m / 3 ^ c with hm₃
  have hsplit : 3 ^ c * m₃ = m := Nat.ordProj_mul_ordCompl_eq_self m 3
  have h3 : ¬ 3 ∣ m₃ := Nat.not_dvd_ordCompl Nat.prime_three hm.ne'
  have hm₃le : m₃ ≤ m := Nat.ordCompl_le m 3
  have hm₃pos : 0 < m₃ := Nat.ordCompl_pos 3 hm.ne'
  have hm₃odd : ¬ 2 ∣ m₃ := fun h => hodd (h.trans ⟨3 ^ c, by rw [← hsplit]; ring⟩)
  have hbase : Covers (2 * 3 ^ (a + c)) := covers_two_mul_three_pow (a + c)
  have hcop : Nat.Coprime m₃ (2 * 3 ^ (a + c)) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact ((Nat.prime_two.coprime_iff_not_dvd).mpr hm₃odd).symm
    · exact Nat.Coprime.pow_right _ (((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm)
  have hsig : 4 * 3 ^ (a + c) ≤ sigma1 (2 * 3 ^ (a + c)) :=
    sigma1_two_mul_three_pow_ge (by omega)
  have hmono : (3 : ℕ) ^ a ≤ 3 ^ (a + c) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbound : m₃ ≤ sigma1 (2 * 3 ^ (a + c)) + 1 := by omega
  have := covers_mul_coprime m₃ (2 * 3 ^ (a + c)) hbase hm₃pos hcop hbound
  have heq : 2 * 3 ^ (a + c) * m₃ = 2 * 3 ^ a * m := by
    rw [pow_add]
    rw [← hsplit]
    ring
  rwa [heq] at this

lemma covers_four_mul_seven_pow_mul {b m : ℕ} (hb : 1 ≤ b) (hm : 0 < m)
    (hle : m ≤ 8 * 7 ^ b) : Covers (4 * 7 ^ b * m) := by
  set v := m.factorization 2 with hv
  set m₄ := m / 2 ^ v with hm₄
  have hsplit2 : 2 ^ v * m₄ = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have h2 : ¬ 2 ∣ m₄ := Nat.not_dvd_ordCompl Nat.prime_two hm.ne'
  have hm₄pos : 0 < m₄ := Nat.ordCompl_pos 2 hm.ne'
  set d := m₄.factorization 7 with hd
  set m₂ := m₄ / 7 ^ d with hm₂
  have hsplit7 : 7 ^ d * m₂ = m₄ := Nat.ordProj_mul_ordCompl_eq_self m₄ 7
  have h7 : ¬ 7 ∣ m₂ := Nat.not_dvd_ordCompl (by norm_num) hm₄pos.ne'
  have hm₂pos : 0 < m₂ := Nat.ordCompl_pos 7 hm₄pos.ne'
  have hm₂le : m₂ ≤ m := le_trans (Nat.ordCompl_le m₄ 7) (Nat.ordCompl_le m 2)
  have hm₂odd : ¬ 2 ∣ m₂ := fun h => h2 (h.trans ⟨7 ^ d, by rw [← hsplit7]; ring⟩)
  have hbase : Covers (2 ^ (2 + v) * 7 ^ (b + d)) :=
    covers_two_pow_mul_seven_pow (by omega) (b + d)
  have hcop : Nat.Coprime m₂ (2 ^ (2 + v) * 7 ^ (b + d)) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact Nat.Coprime.pow_right _ (((Nat.prime_two.coprime_iff_not_dvd).mpr hm₂odd).symm)
    · exact Nat.Coprime.pow_right _ ((((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr h7).symm)
  have hdvd : 4 * 7 ^ b ∣ 2 ^ (2 + v) * 7 ^ (b + d) := by
    refine mul_dvd_mul ?_ ?_
    · have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_dvd_pow 2 (by omega)
    · exact pow_dvd_pow 7 (by omega)
  have hsigd : sigma1 (4 * 7 ^ b) ≤ sigma1 (2 ^ (2 + v) * 7 ^ (b + d)) :=
    sigma1_le_of_dvd (by positivity) hdvd
  have hsig : 8 * 7 ^ b ≤ sigma1 (4 * 7 ^ b) := sigma1_four_mul_seven_pow_ge hb
  have hbound : m₂ ≤ sigma1 (2 ^ (2 + v) * 7 ^ (b + d)) + 1 := by omega
  have hres := covers_mul_coprime m₂ (2 ^ (2 + v) * 7 ^ (b + d)) hbase hm₂pos hcop hbound
  have heq : 2 ^ (2 + v) * 7 ^ (b + d) * m₂ = 4 * 7 ^ b * m := by
    rw [pow_add, pow_add, ← hsplit2, ← hsplit7]
    ring
  rwa [heq] at hres

/-! ## Modular inverse -/

theorem exists_inv_mod (A N : ℕ) (hN : 0 < N) (h : Nat.Coprime A N) :
    ∃ m, 1 ≤ m ∧ m ≤ N ∧ N ∣ A * m + 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  set y : ZMod N := -((A : ZMod N)⁻¹) with hy
  set m₀ := y.val with hm₀
  have h1 : ((m₀ : ℕ) : ZMod N) = y := by rw [hm₀, ZMod.natCast_val, ZMod.cast_id]
  have hcast : ((if m₀ = 0 then N else m₀ : ℕ) : ZMod N) = y := by
    split
    · rename_i h0
      rw [ZMod.natCast_self, ← h1, h0]
      simp
    · exact h1
  refine ⟨if m₀ = 0 then N else m₀, ?_, ?_, ?_⟩
  · split <;> omega
  · split
    · exact le_rfl
    · exact (ZMod.val_lt y).le
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hcast, hy,
      mul_neg, ZMod.coe_mul_inv_eq_one A h]
    ring

/-! ## Choosing matched exponents -/

lemma exists_matched_exponents {b : ℕ} (hb : 1 ≤ b) :
    ∃ a, 1 ≤ a ∧ 7 ^ b ≤ 2 * 3 ^ a ∧ 3 ^ a ≤ 8 * 7 ^ b := by
  have hex : ∃ a, 7 ^ b ≤ 2 * 3 ^ a := by
    refine ⟨3 * b, ?_⟩
    calc 7 ^ b ≤ 27 ^ b := Nat.pow_le_pow_left (by norm_num) b
      _ = 3 ^ (3 * b) := by rw [pow_mul]; norm_num
      _ ≤ 2 * 3 ^ (3 * b) := by omega
  classical
  set a := Nat.find hex with ha
  have hspec : 7 ^ b ≤ 2 * 3 ^ a := Nat.find_spec hex
  have hapos : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h; swap
    · exact h
    · exfalso
      rw [h0] at hspec
      have : (7 : ℕ) ≤ 7 ^ b := by
        calc (7 : ℕ) = 7 ^ 1 := (pow_one 7).symm
          _ ≤ 7 ^ b := Nat.pow_le_pow_right (by norm_num) hb
      simp at hspec
      omega
  refine ⟨a, hapos, hspec, ?_⟩
  have hmin : ¬ (7 ^ b ≤ 2 * 3 ^ (a - 1)) := Nat.find_min hex (by omega)
  push_neg at hmin
  have h3 : (3 : ℕ) ^ a = 3 * 3 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    ring
  omega

/-! ## The construction -/

theorem exists_practical_twin (b : ℕ) (hb : 1 ≤ b) :
    ∃ n, 4 * 7 ^ b ≤ n + 2 ∧ Covers n ∧ Covers (n + 2) := by
  obtain ⟨a, ha, h1, h2⟩ := exists_matched_exponents hb
  have hApos : 0 < 3 ^ a := pow_pos (by norm_num) a
  have hBpos : 0 < 7 ^ b := pow_pos (by norm_num) b
  have hcop : Nat.Coprime (3 ^ a) (2 * 7 ^ b) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact Nat.Coprime.pow_left _ (by norm_num)
    · exact Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨m, hm1, hm2, hmdvd⟩ := exists_inv_mod (3 ^ a) (2 * 7 ^ b) (by omega) hcop
  obtain ⟨m', hm'⟩ := hmdvd
  have hm'pos : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, mul_zero] at hm'; omega
    · exact h
  have heq : 2 * 3 ^ a * m + 2 = 4 * 7 ^ b * m' := by
    calc 2 * 3 ^ a * m + 2 = 2 * (3 ^ a * m + 1) := by ring
      _ = 2 * (2 * 7 ^ b * m') := by rw [hm']
      _ = 4 * 7 ^ b * m' := by ring
  have hm'le : m' ≤ 3 ^ a := by
    by_contra hcon
    push_neg at hcon
    have hstep : 2 * 7 ^ b * (3 ^ a + 1) ≤ 2 * 7 ^ b * m' :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : 2 * 7 ^ b * (3 ^ a + 1) = 2 * (7 ^ b * 3 ^ a) + 2 * 7 ^ b := by ring
    have hsmall : 3 ^ a * m ≤ 2 * (7 ^ b * 3 ^ a) := by
      calc 3 ^ a * m ≤ 3 ^ a * (2 * 7 ^ b) := Nat.mul_le_mul_left _ hm2
        _ = 2 * (7 ^ b * 3 ^ a) := by ring
    have h7 : 2 ≤ 2 * 7 ^ b := by omega
    omega
  have hodd : ¬ 2 ∣ m := by
    intro hd
    have h2dvd : (2 : ℕ) ∣ 3 ^ a * m + 1 := ⟨7 ^ b * m', by rw [hm']; ring⟩
    have hAm : (2 : ℕ) ∣ 3 ^ a * m := Dvd.dvd.mul_left hd (3 ^ a)
    have hsub : (2 : ℕ) ∣ 1 := (Nat.dvd_add_right hAm).mp h2dvd
    omega
  refine ⟨2 * 3 ^ a * m, ?_, ?_, ?_⟩
  · have : 4 * 7 ^ b * 1 ≤ 4 * 7 ^ b * m' := Nat.mul_le_mul_left _ hm'pos
    omega
  · exact covers_two_mul_three_pow_mul ha (by omega) hodd (by omega)
  · rw [heq]
    exact covers_four_mul_seven_pow_mul hb hm'pos (by omega)

/-! ## Main theorem -/

/-- **Practical twin infinitude**: there are infinitely many `n` such that both `n` and
`n + 2` are practical numbers. -/
theorem PracticalTwinInfinitude : {n : ℕ | IsPractical n ∧ IsPractical (n + 2)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hsize, hc1, hc2⟩ := exists_practical_twin (N + 1) (by omega)
  refine ⟨n, ⟨hc1.isPractical, hc2.isPractical⟩, ?_⟩
  have hgrow : N + 1 < 7 ^ (N + 1) := Nat.lt_pow_self (by norm_num)
  omega

end Brockian.PracticalNumbers

