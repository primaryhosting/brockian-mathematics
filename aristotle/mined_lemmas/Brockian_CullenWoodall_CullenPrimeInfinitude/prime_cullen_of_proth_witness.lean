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
