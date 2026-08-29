import Brockian.RieselCovering

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

namespace Brockian.RieselCovering

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is composite
(equivalently, not prime, since these numbers are `> 1`) for every `n ≥ 1`. -/
def IsRieselNumber (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (k * 2 ^ n - 1)

/-- If `p` divides `2 ^ 24 - 1` (i.e. the multiplicative order of `2` mod `p` divides `24`)
and `p ∣ k * 2 ^ r - 1` where `r = n % 24`, then `p ∣ k * 2 ^ n - 1`. -/
theorem dvd_of_period {p k r n : ℕ} (hk : 1 ≤ k) (h24 : p ∣ 2 ^ 24 - 1)
    (hr : p ∣ k * 2 ^ r - 1) (hn : n % 24 = r) : p ∣ k * 2 ^ n - 1 := by
  have hkr : 1 ≤ k * 2 ^ r := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by positivity))
  have hkn : 1 ≤ k * 2 ^ n := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by positivity))
  have h1 : (1 : ℕ) ≡ 2 ^ 24 [MOD p] := (Nat.modEq_iff_dvd' (by norm_num)).mpr h24
  have h2 : (1 : ℕ) ≡ k * 2 ^ r [MOD p] := (Nat.modEq_iff_dvd' hkr).mpr hr
  have h3 : 2 ^ r ≡ 2 ^ n [MOD p] := by
    conv_rhs => rw [← Nat.div_add_mod n 24, hn]
    rw [pow_add, pow_mul]
    calc (2 : ℕ) ^ r = 1 ^ (n / 24) * 2 ^ r := by ring
      _ ≡ (2 ^ 24) ^ (n / 24) * 2 ^ r [MOD p] := Nat.ModEq.mul (h1.pow _) (Nat.ModEq.refl _)
  have h4 : (1 : ℕ) ≡ k * 2 ^ n [MOD p] := h2.trans (Nat.ModEq.mul (Nat.ModEq.refl k) h3)
  exact (Nat.modEq_iff_dvd' hkn).mp h4

/-- The covering system for `k = 509203`: for every residue `r < 24`, one of the primes
`3, 5, 7, 13, 17, 241` divides `509203 * 2 ^ r - 1`. -/
theorem covering_509203 (r : ℕ) (hr : r < 24) :
    ∃ p ∈ [3, 5, 7, 13, 17, 241], p ∣ 509203 * 2 ^ r - 1 := by
  revert hr
  revert r
  decide

/-- Each prime of the covering set has multiplicative order of `2` dividing `24`. -/
theorem covering_primes_period {p : ℕ} (hp : p ∈ [3, 5, 7, 13, 17, 241]) :
    p.Prime ∧ p ≤ 241 ∧ p ∣ 2 ^ 24 - 1 := by
  fin_cases hp <;> refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **509203 is a Riesel number**: it is odd, and `509203 * 2 ^ n - 1` is never prime
for `n ≥ 1`.  This is Riesel's classical construction, proved here via the covering
system `{3, 5, 7, 13, 17, 241}` of period `24`. -/
theorem RieselProblem : IsRieselNumber 509203 := by
  refine ⟨by decide, ?_⟩
  intro n hn hprime
  obtain ⟨p, hpmem, hpdvd⟩ := covering_509203 (n % 24) (Nat.mod_lt _ (by norm_num))
  obtain ⟨hpp, hple, hp24⟩ := covering_primes_period hpmem
  have hdvd : p ∣ 509203 * 2 ^ n - 1 :=
    dvd_of_period (by norm_num) hp24 hpdvd rfl
  have hbig : 509203 * 2 ^ 1 - 1 ≤ 509203 * 2 ^ n - 1 := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have := Nat.mul_le_mul_left 509203 this
    omega
  rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd) with h | h
  · exact hpp.one_lt.ne' h
  · omega

/-- There exists a Riesel number. -/
theorem exists_rieselNumber : ∃ k : ℕ, IsRieselNumber k :=
  ⟨509203, RieselProblem⟩

end Brockian.RieselCovering

