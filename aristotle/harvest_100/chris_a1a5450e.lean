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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists

Category: Brockian Conjecture

Target: `Brockian.SuperperfectNumbers.OddSuperperfectExists`

A natural number `n` is *superperfect* when `σ (σ n) = 2 * n`, where `σ = σ₁` is the
sum-of-divisors function.  The even superperfect numbers are exactly the numbers `2 ^ k`
with `2 ^ (k + 1) - 1` prime; whether an **odd** superperfect number exists is an open
problem.  Accordingly this file does not claim the (open) existence statement.  Instead it
proves unconditional structural facts about a hypothetical odd superperfect number and
packages them as a Lean-checked *conditional reduction*:

* `odd_sigma_of_superperfect`: for every superperfect `n > 0`, `σ n` is odd;
* `isSquare_of_odd_superperfect`: every odd superperfect number is a perfect square
  (Suryanarayana);
* `not_superperfect_of_odd_lt`: there is no odd superperfect number below `4096`;
* `OddSuperperfectExists`: an odd superperfect number exists **iff** there is an odd
  superperfect perfect square that is at least `4096`.
-/

namespace Brockian.SuperperfectNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `n` is *superperfect* when `σ (σ n) = 2 * n`, where `σ` is the sum-of-divisors
function. -/
def Superperfect (n : ℕ) : Prop := σ 1 (σ 1 n) = 2 * n

instance : DecidablePred Superperfect := fun n => by unfold Superperfect; infer_instance

/-- `16` is superperfect: `σ 16 = 31` and `σ 31 = 32 = 2 * 16`. -/
example : Superperfect 16 := by decide

/-- Two distinct divisors of a positive number give a lower bound for its sum of divisors. -/
lemma add_le_sigma_of_dvd {n a b : ℕ} (hn : 0 < n) (ha : a ∣ n) (hb : b ∣ n) (hab : a ≠ b) :
    a + b ≤ σ 1 n := by
  rw [sigma_one_apply]
  have hsub : ({a, b} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Nat.mem_divisors.2 ⟨‹_›, hn.ne'⟩
  calc a + b = ∑ d ∈ ({a, b} : Finset ℕ), d := by rw [Finset.sum_pair hab]
    _ ≤ ∑ d ∈ n.divisors, d := Finset.sum_le_sum_of_subset hsub

/-- `σ (2 ^ a) = 2 ^ (a + 1) - 1`, stated without truncated subtraction. -/
lemma sigma_two_pow_succ (a : ℕ) : σ 1 (2 ^ a) + 1 = 2 ^ (a + 1) := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction a with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ]; omega

/-- If `n` is odd and is not a perfect square, then `σ n` is even: the divisors of `n` are
then partitioned into pairs `{d, n / d}` of two odd numbers. -/
lemma even_sigma_of_odd_of_not_isSquare {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (hsq : ¬ IsSquare n) : Even (σ 1 n) := by
  refine ZMod.natCast_eq_zero_iff_even.mp ?_
  rw [sigma_one_apply, Nat.cast_sum]
  refine Finset.sum_involution (fun d _ => n / d) ?_ ?_ ?_ ?_
  · intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.1 hd).1
    obtain ⟨a, ha⟩ := hodd.of_dvd_nat hdvd
    obtain ⟨b, hb⟩ := hodd.of_dvd_nat (Nat.div_dvd_of_dvd hdvd)
    show ((d : ℕ) : ZMod 2) + ((n / d : ℕ) : ZMod 2) = 0
    rw [hb, ha]
    push_cast
    ring_nf
    simp [show (2 : ZMod 2) = 0 from rfl]
  · intro d hd _ hcon
    simp only at hcon
    exact hsq ⟨d, by
      have hdvd : d ∣ n := (Nat.mem_divisors.1 hd).1
      conv_lhs => rw [← Nat.div_mul_cancel hdvd, hcon]⟩
  · intro d hd
    exact Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.1 hd).1, hn.ne'⟩
  · intro d hd
    exact Nat.div_div_self (Nat.mem_divisors.1 hd).1 hn.ne'

/-- **Key structural result.**  For every positive superperfect number `n`, the value `σ n`
is odd.

Indeed, write `m = σ n` and suppose `m` is even, say `m = 2 ^ a * u` with `a ≥ 1` and `u`
odd.  Then `2 * n = σ m = D * σ u` with `D = σ (2 ^ a) = 2 ^ (a + 1) - 1` odd and `≥ 3`, so
`D ∣ n`; writing `n = D * k` gives `σ u = 2 * k`.  Since `u > 1` we get `σ u ≥ u + 1`, and
`n` has the two distinct divisors `n` and `k`, so
`m = σ n ≥ n + k = 2 ^ a * σ u ≥ 2 ^ a * (u + 1) = m + 2 ^ a > m`, a contradiction. -/
theorem odd_sigma_of_superperfect {n : ℕ} (hn : 0 < n) (hsp : Superperfect n) :
    Odd (σ 1 n) := by
  rw [Superperfect] at hsp
  set m := σ 1 n with hm
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro hev
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hsp
    simp [ArithmeticFunction.map_zero] at hsp
    omega
  set a := m.factorization 2 with hadef
  set u := m / 2 ^ a with hudef
  have hmu : 2 ^ a * u = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have hu0 : u ≠ 0 := by
    intro h; rw [h, Nat.mul_zero] at hmu; exact hm0 hmu.symm
  have ha1 : 1 ≤ a := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hm0 hev.two_dvd
  have hunotdvd : ¬ (2 ∣ u) := Nat.not_dvd_ordCompl Nat.prime_two hm0
  have hcop : Nat.Coprime (2 ^ a) u :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hunotdvd)
  have hmul : σ 1 m = σ 1 (2 ^ a) * σ 1 u := by
    rw [← hmu]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
  set D := σ 1 (2 ^ a) with hDdef
  have hD : D + 1 = 2 ^ (a + 1) := sigma_two_pow_succ a
  have hD3 : 3 ≤ D := by
    have h4 : (4 : ℕ) ≤ 2 ^ (a + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hDodd : ¬ (2 ∣ D) := by
    have h2 : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
    omega
  have h2n : 2 * n = D * σ 1 u := by rw [← hmul, hsp]
  have hDn : D ∣ n :=
    Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hDodd)) ⟨σ 1 u, h2n⟩
  obtain ⟨k, hk⟩ := hDn
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h] at hk; omega
    · exact h
  have hsu : σ 1 u = 2 * k := by
    have h : D * (2 * k) = D * σ 1 u := by rw [← h2n, hk]; ring
    exact (Nat.eq_of_mul_eq_mul_left (by omega) h).symm
  have hu1 : 1 < u := by
    rcases Nat.lt_or_ge u 2 with h | h
    · interval_cases u
      · omega
      · simp at hsu; omega
    · omega
  have hsu_ge : u + 1 ≤ σ 1 u := by
    have := add_le_sigma_of_dvd (n := u) (a := 1) (b := u) (by omega) (one_dvd u) dvd_rfl (by omega)
    omega
  have hkn : k ∣ n := ⟨D, by rw [hk]; ring⟩
  have hkne : n ≠ k := by nlinarith [hk]
  have hbig : n + k ≤ m := by
    have := add_le_sigma_of_dvd (n := n) (a := n) (b := k) hn dvd_rfl hkn hkne
    omega
  have hD2 : D + 1 = 2 ^ a * 2 := by rw [hD]; ring
  have e1 : n + k = 2 ^ a * σ 1 u := by
    rw [hk, hsu]
    calc D * k + k = (D + 1) * k := by ring
      _ = 2 ^ a * 2 * k := by rw [hD2]
      _ = 2 ^ a * (2 * k) := by ring
  have e2 : 2 ^ a * (u + 1) ≤ 2 ^ a * σ 1 u := Nat.mul_le_mul_left _ hsu_ge
  have e3 : 2 ^ a * (u + 1) = m + 2 ^ a := by rw [← hmu]; ring
  have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
  omega

/-- **Suryanarayana's theorem.**  Every odd superperfect number is a perfect square. -/
theorem isSquare_of_odd_superperfect {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (hsp : Superperfect n) : IsSquare n := by
  by_contra hsq
  have h1 : Even (σ 1 n) := even_sigma_of_odd_of_not_isSquare hn hodd hsq
  have h2 : Odd (σ 1 n) := odd_sigma_of_superperfect hn hsp
  exact (Nat.not_even_iff_odd.2 h2) h1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
/-- No odd square `j ^ 2` with `j < 64` is superperfect (a finite kernel computation). -/
lemma not_superperfect_odd_sq_lt_64 : ∀ j ∈ Finset.range 64, Odd j → ¬ Superperfect (j * j) := by
  decide

/-- There is no odd superperfect number below `4096 = 64 ^ 2`. -/
theorem not_superperfect_of_odd_lt {n : ℕ} (hodd : Odd n) (hlt : n < 4096) :
    ¬ Superperfect n := by
  intro hsp
  have hn : 0 < n := hodd.pos
  obtain ⟨j, hj⟩ := isSquare_of_odd_superperfect hn hodd hsp
  have hjodd : Odd j := by
    rcases Nat.even_or_odd j with he | ho
    · exact absurd (hj ▸ he.mul_right j) (Nat.not_even_iff_odd.2 hodd)
    · exact ho
  have hj64 : j < 64 := by nlinarith [hj, hlt]
  exact not_superperfect_odd_sq_lt_64 j (Finset.mem_range.2 hj64) hjodd (hj ▸ hsp)

/-- **Target (conditional reduction).**  Whether an odd superperfect number exists is an
open problem, so we prove instead the following equivalence:  an odd superperfect number
exists **if and only if** there is an odd superperfect number which is moreover a perfect
square and at least `4096`. -/
theorem OddSuperperfectExists :
    (∃ n : ℕ, 0 < n ∧ Odd n ∧ Superperfect n) ↔
      (∃ n : ℕ, 4096 ≤ n ∧ Odd n ∧ IsSquare n ∧ Superperfect n) := by
  constructor
  · rintro ⟨n, hn, hodd, hsp⟩
    refine ⟨n, ?_, hodd, isSquare_of_odd_superperfect hn hodd hsp, hsp⟩
    by_contra h
    exact not_superperfect_of_odd_lt hodd (by omega) hsp
  · rintro ⟨n, hn, hodd, _, hsp⟩
    exact ⟨n, by omega, hodd, hsp⟩

end Brockian.SuperperfectNumbers

