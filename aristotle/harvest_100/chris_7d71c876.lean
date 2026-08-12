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

import Mathlib
/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The infinitude of Cullen primes (i.e. primes of the form `C n = n * 2 ^ n + 1`) is an
open problem, so what is proved here is a *Lean-checked conditional reduction*
together with unconditional partial results:

* `prime_cullen_of_proth_witness` : a Proth-type primality criterion for Cullen numbers
  (sufficiency, proved from scratch via orders in `ZMod q`);
* `exists_proth_witness_of_prime_cullen` : the converse (necessity);
* `CullenPrimeInfinitude` : if for arbitrarily large `n` the Cullen number `C n` has a
  Proth witness, then infinitely many Cullen numbers are prime;
* `cullen_prime_infinitude_iff` : the reduction is in fact an equivalence;
* `dvd_cullen_of_prime_mod_eight`, `infinite_composite_cullen` : unconditionally,
  infinitely many Cullen numbers are composite.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

@[simp] lemma cullen_def (n : ℕ) : cullen n = n * 2 ^ n + 1 := rfl

lemma cullen_one : cullen 1 = 3 := by decide

/-- `C 1 = 3` is a Cullen prime. -/
theorem cullen_one_prime : Nat.Prime (cullen 1) := by
  rw [cullen_one]; norm_num

lemma one_lt_cullen {n : ℕ} (hn : 1 ≤ n) : 1 < cullen n := by
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  simp only [cullen_def]
  nlinarith

lemma cullen_odd (n : ℕ) (hn : 1 ≤ n) : Odd (cullen n) := by
  refine ⟨n * 2 ^ (n - 1), ?_⟩
  have h : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  simp only [cullen_def, h]; ring

/-- Cullen numbers are Proth numbers, since `n < 2 ^ n`. -/
lemma self_lt_two_pow (n : ℕ) : n < 2 ^ n := Nat.lt_two_pow_self

/-- `(C n - 1) / 2 = n * 2 ^ (n - 1)` for `n ≥ 1`. -/
lemma cullen_div_two {n : ℕ} (hn : 1 ≤ n) : cullen n / 2 = n * 2 ^ (n - 1) := by
  have hp2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hval : cullen n = 2 * (n * 2 ^ (n - 1)) + 1 := by
    simp only [cullen_def, hp2]; ring
  omega

/-! ## A Proth-type primality criterion for Cullen numbers -/

/-- **Proth's criterion for Cullen numbers (sufficiency).**  If `n ≥ 1` and there is a
residue `a` modulo `C n` with `a ^ ((C n - 1) / 2) = -1`, then `C n` is prime.
(Here `(C n - 1) / 2 = n * 2 ^ (n - 1)`.) -/
theorem prime_cullen_of_proth_witness (n : ℕ) (hn : 1 ≤ n)
    (a : ZMod (cullen n)) (ha : a ^ (n * 2 ^ (n - 1)) = -1) :
    Nat.Prime (cullen n) := by
  have hN1 : 1 < cullen n := one_lt_cullen hn
  by_contra hnp
  have hqp : (cullen n).minFac.Prime := Nat.minFac_prime (by omega)
  haveI : Fact (cullen n).minFac.Prime := ⟨hqp⟩
  have hqd : (cullen n).minFac ∣ cullen n := Nat.minFac_dvd _
  have hq2 : (cullen n).minFac ≠ 2 := by
    intro h
    have h2 : 2 ∣ cullen n := h ▸ hqd
    obtain ⟨m, hm⟩ := cullen_odd n hn
    omega
  have hbpow : (ZMod.castHom hqd (ZMod (cullen n).minFac) a) ^ (n * 2 ^ (n - 1)) = -1 := by
    rw [← map_pow, ha, map_neg, map_one]
  set b : ZMod (cullen n).minFac := ZMod.castHom hqd (ZMod (cullen n).minFac) a with hb
  have he : 0 < n * 2 ^ (n - 1) := by positivity
  have hbne : b ≠ 0 := by
    intro h
    rw [h, zero_pow he.ne'] at hbpow
    exact one_ne_zero (neg_eq_zero.mp hbpow.symm)
  -- the order of `b` divides `n * 2 ^ n` but not `n * 2 ^ (n - 1)`
  have h1 : b ^ (n * 2 ^ n) = 1 := by
    have hh : n * 2 ^ n = (n * 2 ^ (n - 1)) * 2 := by
      have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      rw [h2]; ring
    rw [hh, pow_mul, hbpow, neg_one_sq]
  have hdvd : orderOf b ∣ n * 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  have hord0 : orderOf b ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hdvd
    have : 0 < n * 2 ^ n := by positivity
    omega
  have hndvd : ¬ orderOf b ∣ n * 2 ^ (n - 1) := by
    intro hd
    have hone : b ^ (n * 2 ^ (n - 1)) = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
    rw [hbpow] at hone
    have h2 : ((2 : ℕ) : ZMod (cullen n).minFac) = 0 := by push_cast; linear_combination -hone
    have hdd := (ZMod.natCast_eq_zero_iff 2 _).mp h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp hdd)
  -- hence `2 ^ n` divides the order of `b`
  set e := (orderOf b).factorization 2 with hedef
  set k := ordCompl[2] (orderOf b) with hkdef
  have hcop : Nat.Coprime 2 k := Nat.coprime_ordCompl Nat.prime_two hord0
  have hkd : k ∣ orderOf b := Nat.ordCompl_dvd _ _
  have heq : 2 ^ e * k = orderOf b := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hkn : k ∣ n :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right n hcop.symm) (hkd.trans hdvd)
  have hen : n ≤ e := by
    by_contra hlt
    push_neg at hlt
    apply hndvd
    have hmm : 2 ^ e * k ∣ 2 ^ (n - 1) * n :=
      mul_dvd_mul (pow_dvd_pow 2 (by omega)) hkn
    rw [← heq, mul_comm n]
    exact hmm
  have h2n : (2 : ℕ) ^ n ∣ orderOf b :=
    (pow_dvd_pow 2 hen).trans (heq ▸ Dvd.intro k rfl)
  -- so the smallest prime factor of `C n` is at least `2 ^ n + 1`, contradicting `q ^ 2 ≤ C n`
  have h2q : (2 : ℕ) ^ n ∣ (cullen n).minFac - 1 :=
    h2n.trans (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hbne))
  have hq2le : 2 ^ n ≤ (cullen n).minFac - 1 :=
    Nat.le_of_dvd (by have := hqp.two_le; omega) h2q
  have hqge : 2 ^ n + 1 ≤ (cullen n).minFac := by have := hqp.two_le; omega
  have hqsq : (cullen n).minFac ^ 2 ≤ cullen n := Nat.minFac_sq_le_self (by omega) hnp
  have hx : (2 ^ n + 1) ^ 2 ≤ (cullen n).minFac ^ 2 := Nat.pow_le_pow_left hqge 2
  have hmul : n * 2 ^ n < 2 ^ n * 2 ^ n :=
    Nat.mul_lt_mul_of_lt_of_le (self_lt_two_pow n) le_rfl (by positivity)
  have hNval : cullen n = n * 2 ^ n + 1 := rfl
  nlinarith [hx, hqsq, hmul, hNval]

/-- **Proth's criterion for Cullen numbers (necessity).**  If `C n` is prime (`n ≥ 1`),
then some `a` satisfies `a ^ ((C n - 1) / 2) = -1` modulo `C n`: any quadratic
non-residue works. -/
theorem exists_proth_witness_of_prime_cullen (n : ℕ) (hn : 1 ≤ n)
    (hpr : Nat.Prime (cullen n)) : ∃ a : ZMod (cullen n), a ^ (n * 2 ^ (n - 1)) = -1 := by
  haveI : Fact (Nat.Prime (cullen n)) := ⟨hpr⟩
  have hp2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hval : cullen n = 2 * (n * 2 ^ (n - 1)) + 1 := by
    simp only [cullen_def, hp2]; ring
  have hge : 1 ≤ n * 2 ^ (n - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hhalf : cullen n / 2 = n * 2 ^ (n - 1) := cullen_div_two hn
  have h3 : 3 ≤ cullen n := by omega
  have hchar : ringChar (ZMod (cullen n)) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have ha0 : a ≠ 0 := by rintro rfl; exact ha IsSquare.zero
  have hne1 : a ^ (cullen n / 2) ≠ 1 := fun hh => ha ((ZMod.euler_criterion _ ha0).mpr hh)
  have hsq : (a ^ (cullen n / 2)) * (a ^ (cullen n / 2)) = 1 := by
    rw [← pow_add]
    have hh : cullen n / 2 + cullen n / 2 = cullen n - 1 := by omega
    rw [hh]
    exact ZMod.pow_card_sub_one_eq_one ha0
  exact ⟨a, hhalf ▸ (mul_self_eq_one_iff.mp hsq).resolve_left hne1⟩

/-! ## The conditional reduction -/

/-- **Conditional infinitude of Cullen primes.**
If for arbitrarily large `n` the Cullen number `C n = n * 2 ^ n + 1` admits a Proth
witness, i.e. some `a` with `a ^ ((C n - 1) / 2) = -1` modulo `C n`, then there are
infinitely many `n` for which `C n` is prime. -/
theorem CullenPrimeInfinitude
    (H : ∀ N : ℕ, ∃ n > N, ∃ a : ZMod (cullen n), a ^ (n * 2 ^ (n - 1)) = -1) :
    {n : ℕ | Nat.Prime (cullen n)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨n, hnN, a, ha⟩ := H N
  exact ⟨n, prime_cullen_of_proth_witness n (by omega) a ha, hnN⟩

/-- The reduction of the previous theorem is sharp: infinitude of Cullen primes is
*equivalent* to the existence of Proth witnesses for arbitrarily large `n`. -/
theorem cullen_prime_infinitude_iff :
    {n : ℕ | Nat.Prime (cullen n)}.Infinite ↔
      ∀ N : ℕ, ∃ n > N, ∃ a : ZMod (cullen n), a ^ (n * 2 ^ (n - 1)) = -1 := by
  refine ⟨fun hinf N => ?_, CullenPrimeInfinitude⟩
  obtain ⟨n, hn, hnN⟩ := hinf.exists_gt N
  exact ⟨n, hnN, exists_proth_witness_of_prime_cullen n (by omega) hn⟩

/-! ## Unconditional partial results: infinitely many composite Cullen numbers -/

/-- If `p` is a prime with `p ≡ 3` or `5 (mod 8)`, i.e. `2` is not a square mod `p`,
then `p` divides the Cullen number `C ((p + 1) / 2)`. -/
theorem dvd_cullen_of_prime_mod_eight (p : ℕ) (hp : Nat.Prime p)
    (h : p % 8 = 3 ∨ p % 8 = 5) : p ∣ cullen ((p + 1) / 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  set m := (p + 1) / 2 with hmdef
  have hm1 : m = p / 2 + 1 := by omega
  have hm : 2 * m = p + 1 := by omega
  have hns : ¬ IsSquare (2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_two_iff hp2]; omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hc : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp hc))
  have hEuler : (2 : ZMod p) ^ (p / 2) ≠ 1 := fun hh => hns ((ZMod.euler_criterion p h2ne).mpr hh)
  have hsq : ((2 : ZMod p) ^ (p / 2)) * ((2 : ZMod p) ^ (p / 2)) = 1 := by
    rw [← pow_add]
    have hh : p / 2 + p / 2 = p - 1 := by omega
    rw [hh]
    exact ZMod.pow_card_sub_one_eq_one h2ne
  have hneg : (2 : ZMod p) ^ (p / 2) = -1 :=
    (mul_self_eq_one_iff.mp hsq).resolve_left hEuler
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [cullen_def]
  push_cast
  have hcast : (2 : ZMod p) ^ m = -2 := by rw [hm1, pow_succ, hneg]; ring
  have hmcast : (2 : ZMod p) * (m : ZMod p) = 1 := by
    have hh : ((2 * m : ℕ) : ZMod p) = ((p + 1 : ℕ) : ZMod p) := by rw [hm]
    push_cast at hh
    simpa [ZMod.natCast_self] using hh
  rw [hcast]
  linear_combination -hmcast

/-- For every prime `p ≡ 3, 5 (mod 8)` the Cullen number `C ((p + 1) / 2)` is composite. -/
theorem not_prime_cullen_of_prime_mod_eight (p : ℕ) (hp : Nat.Prime p)
    (h : p % 8 = 3 ∨ p % 8 = 5) : ¬ Nat.Prime (cullen ((p + 1) / 2)) := by
  intro hpr
  have hdvd := dvd_cullen_of_prime_mod_eight p hp h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set m := (p + 1) / 2 with hmdef
  have hm2 : 2 ≤ m := by omega
  have h4 : 4 ≤ 2 ^ m := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hlt : p < cullen m := by
    have : m * 4 ≤ m * 2 ^ m := Nat.mul_le_mul_left m h4
    simp only [cullen_def]
    omega
  rcases hpr.eq_one_or_self_of_dvd p hdvd with h1 | h1
  · exact hp.one_lt.ne' h1
  · omega

/-- **Unconditionally, there are infinitely many composite Cullen numbers.**
Indeed by Dirichlet's theorem there are infinitely many primes `p ≡ 3 (mod 8)`, and each
of them divides `C ((p + 1) / 2)`. -/
theorem infinite_composite_cullen : {n : ℕ | ¬ Nat.Prime (cullen n)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (2 * N + 1) (q := 8) (a := 3) (by norm_num) (by decide)
  have hmod8 : p % 8 = 3 := by simpa [Nat.ModEq] using hmod
  exact ⟨(p + 1) / 2, not_prime_cullen_of_prime_mod_eight p hp (Or.inl hmod8), by omega⟩

end Brockian.CullenWoodall

