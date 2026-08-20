/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000000

namespace Brockian

/-- `trialDivB n f d` performs trial division of `n` by the successive divisors
`d, d+1, ...` (using at most `f` steps), stopping successfully as soon as the
divisor exceeds `√n`. It returns `true` only when no divisor `≥ d` with
`k * k ≤ n` divides `n`. -/
def trialDivB (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | (f + 1), d => if n % d == 0 then false else if n < (d + 1) * (d + 1) then true
      else trialDivB n f (d + 1)

/-- A kernel-friendly primality test by trial division up to `√n`. -/
def isPrimeB (n : ℕ) : Bool := if n == 2 then true else (2 ≤ n && trialDivB n n 2)

/-- Soundness of the trial-division loop: if it succeeds starting at divisor `d`,
then no `k ≥ d` with `k * k ≤ n` divides `n`. -/
theorem trialDivB_sound :
    ∀ (f n d : ℕ), trialDivB n f d = true → ∀ k, d ≤ k → k * k ≤ n → ¬ k ∣ n := by
  intro f
  induction f with
  | zero => intro n d h; simp [trialDivB] at h
  | succ f ih =>
      intro n d h k hdk hk hdvd
      rw [trialDivB] at h
      by_cases hmod : n % d == 0
      · simp [hmod] at h
      · simp only [hmod] at h
        have hnd : ¬ d ∣ n := by
          intro hd
          exact hmod (by simpa using Nat.mod_eq_zero_of_dvd hd)
        by_cases hlt : n < (d + 1) * (d + 1)
        · -- only `k = d` is possible
          rcases Nat.lt_or_ge k (d + 1) with hk1 | hk1
          · have : k = d := by omega
            exact hnd (this ▸ hdvd)
          · have : (d + 1) * (d + 1) ≤ k * k := Nat.mul_le_mul hk1 hk1
            omega
        · simp only [hlt, if_false] at h
          rcases Nat.lt_or_ge k (d + 1) with hk1 | hk1
          · have : k = d := by omega
            exact hnd (this ▸ hdvd)
          · exact ih n (d + 1) h k hk1 hk hdvd

/-- The Boolean primality test is sound. -/
theorem isPrimeB_prime {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB] at h
  by_cases h2 : n = 2
  · subst h2; exact Nat.prime_two
  · simp only [beq_iff_eq, h2, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hn2, hloop⟩ := h
    refine Nat.prime_def_le_sqrt.mpr ⟨hn2, fun m hm hms => ?_⟩
    exact trialDivB_sound n n 2 hloop m hm (Nat.le_sqrt.mp hms)

/-- **Key intermediate lemma (the wheel check).**
Every even `n` with `4 ≤ n ≤ 2 * 727` has a summand `p < 100` such that both
`p` and `n - p` pass the Boolean primality test. -/
theorem goldbachWheelK2_727_check :
    ∀ n ∈ Finset.Icc 4 1454, n % 2 = 0 →
      ∃ p ∈ Finset.range 100, isPrimeB p ∧ isPrimeB (n - p) := by
  decide

/-- **Goldbach wheel of order `K = 2` at the modulus `727`.**
Every even `n` with `4 ≤ n ≤ 2 * 727` is a sum of two primes, and the smaller
summand can always be taken from the wheel of primes below `100`. -/
theorem GoldbachWheelK2_727 :
    ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 2 * 727 →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n ∧ p < 100 := by
  intro n hev h4 hle
  obtain ⟨p, hp, hp1, hp2⟩ :=
    goldbachWheelK2_727_check n (Finset.mem_Icc.mpr ⟨h4, by omega⟩)
      (Nat.even_iff.mp hev)
  refine ⟨p, n - p, isPrimeB_prime hp1, isPrimeB_prime hp2, ?_, Finset.mem_range.mp hp⟩
  have := (isPrimeB_prime hp2).two_le
  omega

end Brockian

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

