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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

@[simp] lemma woodall_zero : woodall 0 = 0 := rfl

lemma one_le_mul_two_pow {n : ℕ} (hn : 1 ≤ n) : 1 ≤ n * 2 ^ n := by
  have h : 0 < 2 ^ n := Nat.two_pow_pos n
  exact Nat.one_le_iff_ne_zero.2 (by positivity)

lemma woodall_add_one {n : ℕ} (hn : 1 ≤ n) : woodall n + 1 = n * 2 ^ n := by
  have := one_le_mul_two_pow hn
  simp only [woodall]
  omega

/-- `n ↦ n * 2 ^ n` is strictly monotone. -/
lemma mul_two_pow_strictMono : StrictMono (fun n : ℕ => n * 2 ^ n) := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  have h : (n + 1) * 2 ^ (n + 1) = 2 * (n * 2 ^ n) + 2 * 2 ^ n := by ring
  have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
  simp only [h]
  omega

/-- Woodall numbers are strictly increasing from index `1` on. -/
lemma woodall_lt_woodall {m n : ℕ} (hm : 1 ≤ m) (h : m < n) : woodall m < woodall n := by
  have h1 : 1 ≤ m * 2 ^ m := one_le_mul_two_pow hm
  have h2 : m * 2 ^ m < n * 2 ^ n := mul_two_pow_strictMono h
  simp only [woodall]
  omega

lemma woodall_injOn : Set.InjOn woodall {n | 1 ≤ n} := by
  intro a ha b hb hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (Nat.ne_of_lt (woodall_lt_woodall ha h))
  · exact h
  · exact absurd hab.symm (Nat.ne_of_lt (woodall_lt_woodall hb h))

/-! ## Small Woodall primes -/

lemma woodall_two_prime : Nat.Prime (woodall 2) := by decide

lemma woodall_three_prime : Nat.Prime (woodall 3) := by decide

lemma woodall_six_prime : Nat.Prime (woodall 6) := by
  have h : woodall 6 = 383 := by norm_num [woodall]
  rw [h]; norm_num

/-! ## Infinitely many composite Woodall numbers -/

lemma two_pow_odd_mod_three (m : ℕ) : 2 ^ (2 * m + 1) % 3 = 2 := by
  induction m with
  | zero => rfl
  | succ k ih =>
      have h : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by ring
      omega

/-- If `n ≡ 5 [MOD 6]` then `3 ∣ W n`. -/
lemma three_dvd_woodall_of_mod_six (k : ℕ) : 3 ∣ woodall (6 * k + 5) := by
  set n := 6 * k + 5 with hn
  have hpow : 2 ^ n % 3 = 2 := by
    have h : n = 2 * (3 * k + 2) + 1 := by omega
    rw [h]; exact two_pow_odd_mod_three _
  have hmul : n * 2 ^ n % 3 = 1 := by
    conv_lhs => rw [Nat.mul_mod, hpow]
    have h : n % 3 = 2 := by omega
    rw [h]
  have h1 : 1 ≤ n * 2 ^ n := one_le_mul_two_pow (by omega)
  have h2 := Nat.div_add_mod (n * 2 ^ n) 3
  refine ⟨n * 2 ^ n / 3, ?_⟩
  simp only [woodall]
  omega

lemma woodall_gt_three (k : ℕ) : 3 < woodall (6 * k + 5) := by
  have h : 5 * 2 ^ 5 ≤ (6 * k + 5) * 2 ^ (6 * k + 5) := by
    have h1 : (2:ℕ) ^ 5 ≤ 2 ^ (6 * k + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 5 * 2 ^ 5 ≤ 5 * 2 ^ (6 * k + 5) := Nat.mul_le_mul_left _ h1
      _ ≤ (6 * k + 5) * 2 ^ (6 * k + 5) := Nat.mul_le_mul_right _ (by omega)
  simp only [woodall]
  norm_num at h
  omega

/-- Woodall numbers with index `≡ 5 [MOD 6]` are composite, so there are infinitely many
composite Woodall numbers. -/
theorem infinite_composite_woodall : {n : ℕ | ¬ Nat.Prime (woodall n)}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 6 * k + 5) ?_ ?_
  · intro a b hab
    simp only at hab
    omega
  · intro k
    simp only [Set.mem_setOf_eq]
    intro hp
    have hd := three_dvd_woodall_of_mod_six k
    have h3 := woodall_gt_three k
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hd) with h | h <;> omega

/-! ## Every odd prime divides infinitely many Woodall numbers -/

lemma dvd_woodall_iff {p n : ℕ} (hn : 1 ≤ n) [Fact (Nat.Prime p)] :
    p ∣ woodall n ↔ ((n : ZMod p) * 2 ^ n = 1) := by
  have h1 : 1 ≤ n * 2 ^ n := one_le_mul_two_pow hn
  constructor
  · intro h
    have h0 : ((woodall n : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    have h2 : ((n * 2 ^ n : ℕ) : ZMod p) = ((woodall n : ℕ) : ZMod p) + 1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, woodall_add_one hn]
    rw [h0, zero_add] at h2
    push_cast at h2
    exact h2
  · intro h
    have h2 : ((n * 2 ^ n : ℕ) : ZMod p) = 1 := by push_cast; exact h
    have h3 : ((woodall n : ℕ) : ZMod p) = 0 := by
      have h4 : ((woodall n + 1 : ℕ) : ZMod p) = 1 := by rw [woodall_add_one hn]; exact h2
      push_cast at h4 ⊢
      linear_combination h4
    exact (ZMod.natCast_eq_zero_iff _ _).1 h3

/-- For an odd prime `p`, `p` divides `W n` for arbitrarily large `n`.
The witness used is `n = (p-1) * ((p+1)/2 + p * N) + 1`, an element of the arithmetic
progression `n ≡ 1 [MOD p-1]`, `2n ≡ 1 [MOD p]`. -/
theorem odd_prime_dvd_woodall (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (N : ℕ) :
    ∃ n, N < n ∧ p ∣ woodall n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hodd)
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  set m := (p + 1) / 2 with hm
  have h2m : 2 * m = p + 1 := by omega
  set t := m + p * N with ht
  set n := q * t + 1 with hn
  have hNn : N < n := by
    have e1 : N ≤ p * N := Nat.le_mul_of_pos_left N (by omega)
    have e3 : t ≤ q * t := Nat.le_mul_of_pos_left t (by omega)
    omega
  refine ⟨n, hNn, ?_⟩
  rw [dvd_woodall_iff (by omega)]
  have hpz : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hfer : ((2 : ZMod p)) ^ q = 1 := by
    have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    have h3 := ZMod.pow_card_sub_one_eq_one (p := p) (a := ((2 : ℕ) : ZMod p)) h2
    have hq1 : p - 1 = q := by omega
    rw [hq1] at h3
    simpa using h3
  have hpow : (2 : ZMod p) ^ n = 2 := by
    rw [hn, pow_succ, pow_mul, hfer, one_pow, one_mul]
  rw [hpow]
  have hqz : ((q : ℕ) : ZMod p) = -1 := by
    have h : ((p : ℕ) : ZMod p) = ((q + 1 : ℕ) : ZMod p) := by rw [← hq]
    rw [hpz] at h
    push_cast at h
    linear_combination -h
  have htz : ((t : ℕ) : ZMod p) = ((m : ℕ) : ZMod p) := by
    rw [ht]
    push_cast [hpz]
    ring
  have hnz : ((n : ℕ) : ZMod p) = 1 - ((m : ℕ) : ZMod p) := by
    rw [hn]
    push_cast [hqz, htz]
    ring
  have hmz : 2 * ((m : ℕ) : ZMod p) = 1 := by
    have h : ((2 * m : ℕ) : ZMod p) = ((p + 1 : ℕ) : ZMod p) := by rw [h2m]
    push_cast at h
    rw [hpz] at h
    linear_combination h
  rw [hnz]
  linear_combination -hmz

/-! ## Main conditional theorem -/

/-- **Woodall prime infinitude (conditional).**  The infinitude of the set of Woodall primes
follows from the (open) statement that Woodall primes occur with arbitrarily large index.
This is a genuine reduction: from unboundedness of the *index* set one obtains infinitude of
the set of *primes* of the form `n * 2 ^ n - 1`, using strict monotonicity of the Woodall
numbers. -/
theorem WoodallPrimeInfinitude
    (h : ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (woodall n)) :
    {q : ℕ | q.Prime ∧ ∃ n, 1 ≤ n ∧ q = woodall n}.Infinite := by
  have hidx : {n : ℕ | 1 ≤ n ∧ Nat.Prime (woodall n)}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨n, hn, hnp⟩ := h N
    have h1 : 1 ≤ n := by
      by_contra hc
      have hz : n = 0 := by omega
      rw [hz, woodall_zero] at hnp
      exact Nat.not_prime_zero hnp
    have := hN (show n ∈ {n : ℕ | 1 ≤ n ∧ Nat.Prime (woodall n)} from ⟨h1, hnp⟩)
    omega
  have hinj : Set.InjOn woodall {n : ℕ | 1 ≤ n ∧ Nat.Prime (woodall n)} :=
    fun a ha b hb hab => woodall_injOn ha.1 hb.1 hab
  apply (hidx.image hinj).mono
  rintro _ ⟨n, ⟨h1, hp⟩, rfl⟩
  exact ⟨hp, n, h1, rfl⟩

/-- The hypothesis of `WoodallPrimeInfinitude` is not merely sufficient but necessary:
the set of Woodall primes is infinite **iff** Woodall primes occur with arbitrarily large
index.  Thus the reduction above is sharp. -/
theorem woodall_prime_infinite_iff :
    {q : ℕ | q.Prime ∧ ∃ n, 1 ≤ n ∧ q = woodall n}.Infinite ↔
      ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (woodall n) := by
  refine ⟨fun hinf N => ?_, WoodallPrimeInfinitude⟩
  obtain ⟨q, ⟨hq, n, h1, rfl⟩, hlt⟩ := hinf.exists_gt (woodall N)
  refine ⟨n, ?_, hq⟩
  by_contra hc
  have hnN : n ≤ N := by omega
  rcases eq_or_lt_of_le hnN with h | h
  · subst h; omega
  · exact absurd (woodall_lt_woodall h1 h) (by omega)

/-! ## Cullen companion: every odd prime divides a Cullen number -/

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- Classical fact: for an odd prime `p` we have `p ∣ C (p - 2)`. -/
theorem odd_prime_dvd_cullen (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) : p ∣ cullen (p - 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  set k := p - 2 with hk
  have hpz : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hkz : ((k : ℕ) : ZMod p) = -2 := by
    have h : ((k + 2 : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) := by
      congr 1
      omega
    rw [hpz] at h
    push_cast at h
    linear_combination h
  have hfer : (2 : ZMod p) ^ k * 2 = 1 := by
    have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    have h3 := ZMod.pow_card_sub_one_eq_one (p := p) (a := ((2 : ℕ) : ZMod p)) h2
    have hkp : k + 1 = p - 1 := by omega
    have : (2 : ZMod p) ^ (k + 1) = 1 := by
      rw [hkp]; simpa using h3
    rwa [pow_succ] at this
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [cullen]
  push_cast [hkz]
  linear_combination -hfer

end CullenWoodall
end Brockian

