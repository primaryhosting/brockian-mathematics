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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RieselCovering

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is never prime
for `n ≥ 1`. -/
def IsRieselNumber (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (k * 2 ^ n - 1)

/-- If `2 ^ 24 ≡ 1 [MOD p]` then `2 ^ n` only depends on `n % 24` modulo `p`. -/
lemma two_pow_modEq_two_pow_mod (p n : ℕ) (hp : 2 ^ 24 ≡ 1 [MOD p]) :
    2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
  conv_lhs => rw [← Nat.div_add_mod n 24]
  calc 2 ^ (24 * (n / 24) + n % 24)
      = (2 ^ 24) ^ (n / 24) * 2 ^ (n % 24) := by rw [pow_add, pow_mul]
    _ ≡ 1 ^ (n / 24) * 2 ^ (n % 24) [MOD p] := Nat.ModEq.mul (hp.pow _) (Nat.ModEq.refl _)
    _ = 2 ^ (n % 24) := by rw [one_pow, one_mul]

/-- Transfer of a divisibility `p ∣ 509203 * 2 ^ r - 1` from the residue `r = n % 24`
to the exponent `n` itself, given that `2` has order dividing `24` modulo `p`. -/
lemma dvd_of_dvd_residue (p r n : ℕ) (h24 : 2 ^ 24 ≡ 1 [MOD p]) (hr : n % 24 = r)
    (hd : p ∣ 509203 * 2 ^ r - 1) : p ∣ 509203 * 2 ^ n - 1 := by
  have h1 : ∀ m : ℕ, 1 ≤ 509203 * 2 ^ m := by
    intro m
    have : 0 < 2 ^ m := pow_pos (by norm_num) m
    nlinarith
  have hone : 1 ≡ 509203 * 2 ^ r [MOD p] := (Nat.modEq_iff_dvd' (h1 r)).mpr hd
  have hstep : 509203 * 2 ^ r ≡ 509203 * 2 ^ n [MOD p] := by
    have := (two_pow_modEq_two_pow_mod p n h24).symm
    rw [hr] at this
    exact Nat.ModEq.mul_left _ this
  exact (Nat.modEq_iff_dvd' (h1 n)).mp (hone.trans hstep)

/-- The covering set `{3, 5, 7, 13, 17, 241}` for `k = 509203`: for every exponent `n`
one of these primes divides `509203 * 2 ^ n - 1`. -/
lemma exists_small_prime_dvd (n : ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 241 ∧ p ∣ 509203 * 2 ^ n - 1 := by
  obtain ⟨r, hr, hrlt⟩ : ∃ r, n % 24 = r ∧ r < 24 :=
    ⟨n % 24, rfl, Nat.mod_lt _ (by norm_num)⟩
  interval_cases r
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 0 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 1 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 2 n (by decide) hr (by norm_num)⟩
  · exact ⟨241, by norm_num, by norm_num, dvd_of_dvd_residue 241 3 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 4 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 5 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 6 n (by decide) hr (by norm_num)⟩
  · exact ⟨13, by norm_num, by norm_num, dvd_of_dvd_residue 13 7 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 8 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 9 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 10 n (by decide) hr (by norm_num)⟩
  · exact ⟨7, by norm_num, by norm_num, dvd_of_dvd_residue 7 11 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 12 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 13 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 14 n (by decide) hr (by norm_num)⟩
  · exact ⟨17, by norm_num, by norm_num, dvd_of_dvd_residue 17 15 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 16 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 17 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 18 n (by decide) hr (by norm_num)⟩
  · exact ⟨13, by norm_num, by norm_num, dvd_of_dvd_residue 13 19 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 20 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 21 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 22 n (by decide) hr (by norm_num)⟩
  · exact ⟨7, by norm_num, by norm_num, dvd_of_dvd_residue 7 23 n (by decide) hr (by norm_num)⟩

/-- **The Riesel problem**: `509203` is a Riesel number, i.e. it is odd and
`509203 * 2 ^ n - 1` is composite for every `n ≥ 1`.  The proof uses Riesel's covering
system `{3, 5, 7, 13, 17, 241}`, whose primes all satisfy `2 ^ 24 ≡ 1`: for each residue
`r = n % 24` one of them divides `509203 * 2 ^ n - 1`. -/
theorem RieselProblem : IsRieselNumber 509203 := by
  refine ⟨⟨254601, by norm_num⟩, ?_⟩
  intro n hn hprime
  obtain ⟨p, hp, hple, hdvd⟩ := exists_small_prime_dvd n
  have hbig : 1018405 ≤ 509203 * 2 ^ n - 1 := by
    have h2 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 509203 * 2 ^ 1 ≤ 509203 * 2 ^ n := Nat.mul_le_mul_left _ h2
    omega
  rcases (hprime.eq_one_or_self_of_dvd p hdvd) with h | h
  · exact hp.one_lt.ne' h
  · omega

end Brockian.RieselCovering

