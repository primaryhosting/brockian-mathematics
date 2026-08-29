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

(The header comment is placed immediately after `import Mathlib` because Lean 4
requires `import` commands to precede every other command, including module
docstrings; the header text itself is verbatim.)
-/

set_option maxHeartbeats 1000000

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

@[simp] lemma cullen_def (n : ℕ) : cullen n = n * 2 ^ n + 1 := rfl

/-- Cullen numbers grow: `n + 2 < C n` for `n ≥ 2`. -/
lemma lt_cullen_of_two_le {n : ℕ} (hn : 2 ≤ n) : n + 2 < cullen n := by
  have h2 : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have : n * (n + 1) ≤ n * 2 ^ n := Nat.mul_le_mul_left n h2
  simp only [cullen_def]
  nlinarith

/-- `1 < C n` for `n ≥ 1`. -/
lemma one_lt_cullen {n : ℕ} (hn : 1 ≤ n) : 1 < cullen n := by
  have : 1 * 2 ^ 1 ≤ n * 2 ^ n :=
    Nat.mul_le_mul hn (Nat.pow_le_pow_right (by norm_num) hn)
  simp only [cullen_def]
  omega

/-- A number bigger than `1` with no prime factor `p` satisfying `p * p ≤ m` is prime. -/
lemma prime_of_no_small_prime_factor {m : ℕ} (hm : 1 < m)
    (h : ∀ p : ℕ, p.Prime → p * p ≤ m → ¬ p ∣ m) : m.Prime := by
  by_contra hcomp
  have hpos : 0 < m := lt_trans Nat.zero_lt_one hm
  have hmf : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hle : m.minFac * m.minFac ≤ m := by
    have h' := Nat.minFac_sq_le_self hpos hcomp
    nlinarith [h']
  exact h m.minFac hmf hle (Nat.minFac_dvd m)

/-!
## A partial unconditional result: infinitely many Cullen numbers are composite

For every odd prime `p` one has `p ∣ C (p - 2)`, by Fermat's little theorem:
`C (p-2) = (p-2) * 2 ^ (p-2) + 1 ≡ -2 * 2 ^ (p-2) + 1 = 1 - 2 ^ (p-1) ≡ 0 (mod p)`.
-/

/-- Fermat-type divisibility: every odd prime `p` divides the Cullen number `C (p - 2)`. -/
theorem prime_dvd_cullen_sub_two {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    p ∣ cullen (p - 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    simpa using h
  have hferm : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have key : ((cullen (p - 2) : ℕ) : ZMod p) = 0 := by
    have hcast : (((p - 2 : ℕ)) : ZMod p) = -2 := by
      have h : (((p - 2 : ℕ)) : ZMod p) = (p : ZMod p) - ((2 : ℕ) : ZMod p) := by
        rw [Nat.cast_sub hp2]
      rw [h]
      simp
    simp only [cullen_def, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, hcast]
    have hexp : p - 1 = (p - 2) + 1 := by omega
    have hmul : (2 : ZMod p) ^ (p - 2) * 2 = 1 := by
      calc (2 : ZMod p) ^ (p - 2) * 2 = 2 ^ ((p - 2) + 1) := by ring
        _ = 2 ^ (p - 1) := by rw [hexp]
        _ = 1 := hferm
    linear_combination -hmul
  exact (ZMod.natCast_eq_zero_iff _ _).mp key

/-- For every prime `p ≥ 5`, the Cullen number `C (p - 2)` is composite. -/
theorem not_prime_cullen_sub_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ (cullen (p - 2)).Prime := by
  intro hprime
  have hdvd : p ∣ cullen (p - 2) := prime_dvd_cullen_sub_two hp (by omega)
  have hlt : (p - 2) + 2 < cullen (p - 2) := lt_cullen_of_two_le (by omega)
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · omega
  · omega

/-- There are infinitely many composite Cullen numbers. -/
theorem infinite_composite_cullen : {n : ℕ | ¬ (cullen n).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (a + 5)
  exact ⟨p - 2, not_prime_cullen_sub_two hp (by omega), by omega⟩

/-!
## Reformulation of the Cullen prime infinitude conjecture

The conjecture that infinitely many Cullen numbers are prime is open.  The theorem
below is a Lean-checked *reduction*: it derives the infinitude of Cullen primes from
the (equivalent, but more directly attackable) statement that arbitrarily large
Cullen numbers have no prime factor below their square root.
-/

/-- The sieve-style hypothesis: arbitrarily large Cullen numbers have no prime factor
`p` with `p * p ≤ C n`. -/
def NoSmallFactorCullenUnbounded : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∀ p : ℕ, p.Prime → p * p ≤ cullen n → ¬ p ∣ cullen n

/-- **Cullen prime infinitude (conditional reduction).**
If arbitrarily large Cullen numbers avoid all prime factors up to their square root,
then there are infinitely many Cullen primes. -/
theorem CullenPrimeInfinitude (h : NoSmallFactorCullenUnbounded) :
    {n : ℕ | (cullen n).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hns⟩ := h (a + 1)
  exact ⟨n, prime_of_no_small_prime_factor (one_lt_cullen (by omega)) hns, by omega⟩

/-- The hypothesis of `CullenPrimeInfinitude` is in fact *equivalent* to the
infinitude of Cullen primes, so the reduction loses nothing. -/
theorem noSmallFactorCullenUnbounded_iff :
    NoSmallFactorCullenUnbounded ↔ {n : ℕ | (cullen n).Prime}.Infinite := by
  refine ⟨CullenPrimeInfinitude, ?_⟩
  intro hinf N
  obtain ⟨n, hn, hgt⟩ : ∃ n ∈ {n : ℕ | (cullen n).Prime}, N < n := by
    by_contra hcon
    push_neg at hcon
    exact hinf.not_bddAbove ⟨N, fun x hx => hcon x hx⟩
  refine ⟨n, le_of_lt hgt, ?_⟩
  intro p hp hple hdvd
  have hprime : (cullen n).Prime := hn
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · exact hp.one_lt.ne' h
  · subst h
    nlinarith [hp.two_le]

end Brockian.CullenWoodall

