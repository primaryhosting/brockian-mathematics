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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

/-- A Carmichael number: a composite `n > 1` such that Fermat's little theorem
congruence `a ^ (n - 1) ≡ 1 [MOD n]` holds for every `a` coprime to `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, Nat.Coprime a n → a ^ (n - 1) ≡ 1 [MOD n]

/-- The Chernick–Dickson hypothesis: there are infinitely many `k` for which
`6k+1`, `12k+1` and `18k+1` are simultaneously prime.  This is a special case of
Dickson's conjecture (and of the Hardy–Littlewood prime `k`-tuples conjecture);
it is not known unconditionally. -/
def ChernickDicksonHypothesis : Prop :=
  ∀ N : ℕ, ∃ k, N < k ∧ Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧
    Nat.Prime (18 * k + 1)

/-- Local Korselt step: if `p` is prime and `p - 1 ∣ n - 1` (with `n ≥ 1`), then
`a ^ n ≡ a [MOD p]` for every `a`. -/
lemma pow_modEq_self_of_sub_one_dvd {p n a : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (h : (p - 1) ∣ (n - 1)) : a ^ n ≡ a [MOD p] := by
  obtain ⟨m, hm⟩ := h
  have hnn : n = (p - 1) * m + 1 := by omega
  by_cases hpa : p ∣ a
  · have h0 : a ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 hpa
    calc a ^ n ≡ 0 ^ n [MOD p] := h0.pow n
      _ = 0 := zero_pow (by omega)
      _ ≡ a [MOD p] := h0.symm
  · have hcop : Nat.Coprime a p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa))
    have hfermat : a ^ (p - 1) ≡ 1 [MOD p] := by
      have := Nat.ModEq.pow_totient hcop
      rwa [Nat.totient_prime hp] at this
    calc a ^ n = (a ^ (p - 1)) ^ m * a := by rw [hnn, pow_succ, pow_mul]
      _ ≡ 1 ^ m * a [MOD p] := Nat.ModEq.mul (hfermat.pow m) (Nat.ModEq.refl a)
      _ = a := by ring

/-- Korselt's criterion for a product of three distinct primes. -/
lemma isCarmichael_of_three_primes {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r)
    (hdp : (p - 1) ∣ (p * q * r - 1)) (hdq : (q - 1) ∣ (p * q * r - 1))
    (hdr : (r - 1) ∣ (p * q * r - 1)) : IsCarmichael (p * q * r) := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  set n := p * q * r with hn
  have hqr1 : 1 < q * r := by nlinarith
  have hn1 : 1 < n := by
    have : 1 * 1 < p * (q * r) := by nlinarith
    simpa [hn, mul_assoc] using this
  refine ⟨hn1, ?_, ?_⟩
  · rw [hn, mul_assoc]
    exact Nat.not_prime_mul (by omega) (by omega)
  · intro a hcop
    -- Korselt at each prime
    have hmp : a ^ n ≡ a [MOD p] := pow_modEq_self_of_sub_one_dvd hp (by omega) hdp
    have hmq : a ^ n ≡ a [MOD q] := pow_modEq_self_of_sub_one_dvd hq (by omega) hdq
    have hmr : a ^ n ≡ a [MOD r] := pow_modEq_self_of_sub_one_dvd hr (by omega) hdr
    have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 (by omega)
    have hcpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).2 (by omega)
    have hcqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 (by omega)
    have hpq' : a ^ n ≡ a [MOD p * q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcpq).1 ⟨hmp, hmq⟩
    have hcpqr : Nat.Coprime (p * q) r := Nat.Coprime.mul_left hcpr hcqr
    have hall : a ^ n ≡ a [MOD n] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcpqr).1 ⟨hpq', hmr⟩
    -- cancel one factor of `a`
    have hstep : a * a ^ (n - 1) ≡ a * 1 [MOD n] := by
      have : a * a ^ (n - 1) = a ^ n := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this, mul_one]
      exact hall
    exact Nat.ModEq.cancel_left_of_coprime hcop.symm hstep

/-- A product of three distinct primes has exactly three prime factors. -/
lemma primeFactors_card_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) : (p * q * r).primeFactors.card = 3 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq0 : q ≠ 0 := hq.ne_zero
  have hr0 : r ≠ 0 := hr.ne_zero
  rw [Nat.primeFactors_mul (by positivity) hr0, Nat.primeFactors_mul hp0 hq0,
    hp.primeFactors, hq.primeFactors, hr.primeFactors]
  rw [Finset.card_eq_three]
  exact ⟨p, q, r, by omega, by omega, by omega, by simp⟩

/-- Chernick's construction: if `6k+1`, `12k+1`, `18k+1` are all prime and `k ≥ 1`,
then their product is a Carmichael number with exactly three prime factors. -/
lemma chernick_carmichael {k : ℕ} (hk : 1 ≤ k) (h6 : Nat.Prime (6 * k + 1))
    (h12 : Nat.Prime (12 * k + 1)) (h18 : Nat.Prime (18 * k + 1)) :
    IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) ∧
      ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)).primeFactors.card = 3 := by
  have hlt1 : 6 * k + 1 < 12 * k + 1 := by omega
  have hlt2 : 12 * k + 1 < 18 * k + 1 := by omega
  have hplus : (6 * k + 1) * (12 * k + 1) * (18 * k + 1)
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) + 1 := by ring
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by omega
  have e6 : (6 * k + 1) - 1 = 6 * k := by omega
  have e12 : (12 * k + 1) - 1 = 12 * k := by omega
  have e18 : (18 * k + 1) - 1 = 18 * k := by omega
  refine ⟨isCarmichael_of_three_primes h6 h12 h18 hlt1 hlt2 ?_ ?_ ?_,
    primeFactors_card_three h6 h12 h18 hlt1 hlt2⟩
  · rw [e6, hsub]; exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  · rw [e12, hsub]; exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  · rw [e18, hsub]; exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by ring⟩

/-- **Three Prime Carmichael Infinitude** (conditional).

Assuming the Chernick–Dickson hypothesis — that `6k+1`, `12k+1`, `18k+1` are
simultaneously prime for infinitely many `k`, a special case of Dickson's
conjecture — there are infinitely many Carmichael numbers with exactly three
prime factors.

The unconditional statement is an open problem; this is a Lean-checked
conditional reduction of it to the stated prime-tuple hypothesis. -/
theorem ThreePrimeCarmichaelInfinitude (H : ChernickDicksonHypothesis) :
    {n : ℕ | IsCarmichael n ∧ n.primeFactors.card = 3}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨k, hk, h6, h12, h18⟩ := H (N + 1)
  refine ⟨(6 * k + 1) * (12 * k + 1) * (18 * k + 1), chernick_carmichael (by omega) h6 h12 h18, ?_⟩
  calc N < 6 * k + 1 := by omega
    _ ≤ (6 * k + 1) * ((12 * k + 1) * (18 * k + 1)) :=
        Nat.le_mul_of_pos_right _ (by positivity)
    _ = (6 * k + 1) * (12 * k + 1) * (18 * k + 1) := by ring

/-- Non-vacuity of the construction: `1729 = 7 · 13 · 19` (the case `k = 1`) is a
Carmichael number with exactly three prime factors. -/
lemma isCarmichael_1729 : IsCarmichael 1729 ∧ (1729 : ℕ).primeFactors.card = 3 := by
  have h := chernick_carmichael (k := 1) le_rfl (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

end Brockian.CarmichaelKorselt

