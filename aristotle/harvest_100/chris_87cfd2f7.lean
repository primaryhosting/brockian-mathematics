/-
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace CS

open Polynomial

/-- If `p` is a prime dividing `n`, then `p` does not divide `(n-1).choose (p-1)`.
Indeed, by Lucas' theorem this binomial coefficient is `≡ 1 [MOD p]`. -/
theorem not_dvd_choose_pred (p n : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn : 1 ≤ n) :
    ¬ p ∣ (n - 1).choose (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 2 ≤ p := hp.two_le
  have hmod : (n - 1) % p = p - 1 := by
    obtain ⟨t, rfl⟩ := hpn
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · simp [h] at hn
      · exact h
    obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + 1 := ⟨t - 1, by omega⟩
    have hexp : p * (s + 1) = p * s + p := by ring
    have hrw : p * (s + 1) - 1 = p * s + (p - 1) := by omega
    rw [hrw, Nat.mul_add_mod, Nat.mod_eq_of_lt (show p - 1 < p by omega)]
  have key := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n - 1) (k := p - 1) (p := p)
  rw [hmod, Nat.mod_eq_of_lt (show p - 1 < p by omega),
    Nat.div_eq_of_lt (show p - 1 < p by omega), Nat.choose_self, Nat.choose_zero_right,
    Nat.mul_one] at key
  intro hdvd
  have hkey : (n - 1).choose (p - 1) % p = 1 % p := key
  rw [Nat.dvd_iff_mod_eq_zero.mp hdvd, Nat.mod_eq_of_lt hp.one_lt] at hkey
  exact absurd hkey (by omega)

/-- If `p` is a prime dividing `n` and `2 ≤ n`, then `n` does not divide `n.choose p`. -/
theorem not_dvd_choose (p n : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn : 2 ≤ n) :
    ¬ n ∣ n.choose p := by
  intro ⟨m, hm⟩
  have hkey : n * ((n - 1).choose (p - 1)) = n.choose p * p := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (p - 1)
    have h1 : n - 1 + 1 = n := by omega
    have h2 : p - 1 + 1 = p := by omega
    rw [h1, h2] at h
    exact h
  rw [hm] at hkey
  have hn0 : 0 < n := by omega
  have : (n - 1).choose (p - 1) = m * p := by
    have : n * ((n - 1).choose (p - 1)) = n * (m * p) := by rw [hkey]; ring
    exact Nat.eq_of_mul_eq_mul_left hn0 this
  exact not_dvd_choose_pred p n hp hpn (by omega) ⟨m, by rw [this]; ring⟩

/--
**AKS criterion (Agrawal–Kayal–Saxena, Lemma 2.1)**, the number-theoretic heart of the
"PRIMES is in P" theorem.

For `n ≥ 2` and `a` coprime to `n`, the number `n` is prime if and only if the polynomial
identity `(X + a) ^ n = X ^ n + a` holds in `(ZMod n)[X]`.
-/
theorem aks_primes_in_p (n a : ℕ) (hn : 2 ≤ n) (ha : Nat.Coprime a n) :
    Nat.Prime n ↔
      (X + C (a : ZMod n)) ^ n = X ^ n + C (a : ZMod n) := by
  constructor
  · intro hprime
    haveI : Fact n.Prime := ⟨hprime⟩
    haveI : CharP (ZMod n) n := ZMod.charP n
    haveI : ExpChar (ZMod n)[X] n := by
      have : CharP (ZMod n)[X] n := inferInstance
      exact ExpChar.prime hprime
    rw [add_pow_char]
    congr 1
    rw [← C_pow, ZMod.pow_card]
  · intro hid
    by_contra hnp
    -- pick a prime factor `p` of `n`; it satisfies `p < n`
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have hplt : p < n := by
      rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hpn) with h | h
      · exact h
      · exact absurd (h ▸ hp) hnp
    -- compare the coefficients of `X ^ p`
    have hcoeff := congrArg (fun q => Polynomial.coeff q p) hid
    simp only [coeff_X_add_C_pow, coeff_add, coeff_X_pow, coeff_C] at hcoeff
    have hp0 : 0 < p := hp.pos
    rw [if_neg (by omega), if_neg (by omega : ¬ p = 0)] at hcoeff
    -- so `n ∣ n.choose p`, using that `a` is a unit mod `n`
    have hazero : ((a : ZMod n))^(n - p) * (n.choose p : ZMod n) = 0 := by
      simpa using hcoeff
    have hunit : IsUnit ((a : ZMod n)) := (ZMod.isUnit_iff_coprime a n).2 ha
    have hunit' : IsUnit (((a : ZMod n))^(n - p)) := hunit.pow _
    have hzero : ((n.choose p : ℕ) : ZMod n) = 0 := by
      rcases hunit' with ⟨u, hu⟩
      have := congrArg (fun x => (↑u⁻¹ : ZMod n) * x) hazero
      simpa [← hu, ← mul_assoc] using this
    have hdvd : n ∣ n.choose p := (ZMod.natCast_eq_zero_iff _ _).1 hzero
    exact not_dvd_choose p n hp hpn hn hdvd

end CS

