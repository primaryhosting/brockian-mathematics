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

namespace Brockian
namespace SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/
noncomputable def sig (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

lemma sig_eq_sum (n : ℕ) : sig n = ∑ d ∈ n.divisors, d := by
  simp [sig, ArithmeticFunction.sigma_one_apply]

/-- `n` is *superperfect* when `σ(σ(n)) = 2n`. -/
def Superperfect (n : ℕ) : Prop := sig (sig n) = 2 * n

lemma sig_prime {p : ℕ} (hp : p.Prime) : sig p = p + 1 := by
  simp [sig, ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors hp]

lemma sig_two_pow (a : ℕ) : sig (2 ^ a) = 2 ^ (a + 1) - 1 := by
  rw [sig_eq_sum, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction a with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih]
    have : 1 ≤ 2 ^ (b + 1) := Nat.one_le_two_pow
    ring_nf
    omega

lemma le_sig {n : ℕ} (hn : 1 < n) : n + 1 ≤ sig n := by
  rw [sig_eq_sum]
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [Nat.mem_divisors] <;> omega
  calc n + 1 = ∑ d ∈ ({1, n} : Finset ℕ), d := by
        rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ n)]; omega
    _ ≤ ∑ d ∈ n.divisors, d := Finset.sum_le_sum_of_subset hsub

lemma sig_ne_two (k : ℕ) : sig k ≠ 2 := by
  match k with
  | 0 => simp [sig_eq_sum]
  | 1 => simp [sig_eq_sum]
  | (m + 2) => have := le_sig (n := m + 2) (by omega); omega

lemma sig_ne_zero {n : ℕ} (hn : n ≠ 0) : sig n ≠ 0 := by
  have : 1 ≤ ∑ d ∈ n.divisors, d :=
    Finset.single_le_sum (f := fun d => d) (by intros; positivity) (Nat.one_mem_divisors.mpr hn)
  rw [sig_eq_sum]; omega

/-- Structure of an odd superperfect number: writing `σ(n) = 2 ^ a * k` with `k` odd,
one has `(2 ^ (a+1) - 1) * σ(k) = 2n`; in particular the Mersenne number `2 ^ (a+1) - 1`
divides `n`. -/
lemma odd_superperfect_structure {n : ℕ} (hn : Odd n) (hs : Superperfect n) :
    ∃ a k, Odd k ∧ sig n = 2 ^ a * k ∧ (2 ^ (a + 1) - 1) * sig k = 2 * n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨a, k, hk, hm⟩ := Nat.exists_eq_two_pow_mul_odd (sig_ne_zero hn0)
  refine ⟨a, k, hk, hm, ?_⟩
  have hcop : Nat.gcd (2 ^ a) k = 1 :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hk)
  have h2 := hs
  rw [Superperfect, hm, show sig (2 ^ a * k) = sig (2 ^ a) * sig k from
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_sigma hcop, sig_two_pow] at h2
  exact h2

/-- No odd prime is superperfect. -/
lemma not_superperfect_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) : ¬ Superperfect p := by
  intro hs
  obtain ⟨a, k, hk, hm, heq⟩ := odd_superperfect_structure hodd hs
  rw [sig_prime hp] at hm
  have ha : 1 ≤ a := by
    by_contra h
    interval_cases a
    · simp at hm
      obtain ⟨t, ht⟩ := hodd
      obtain ⟨s, hs'⟩ := hk
      omega
  set q := 2 ^ (a + 1) - 1 with hq
  have hqodd : Odd q := by
    have h1 : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
    obtain ⟨c, hc⟩ : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
    exact ⟨c - 1, by omega⟩
  have hqdvd : q ∣ 2 * p := ⟨sig k, heq.symm⟩
  have hqp : q ∣ p := Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hqodd) hqdvd
  have hq3 : 3 ≤ q := by
    have : 2 ^ 2 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hqeq : q = p := (hp.eq_one_or_self_of_dvd q hqp).resolve_left (by omega)
  rw [hqeq] at heq
  have hsk : p * sig k = p * 2 := by rw [heq]; ring
  exact sig_ne_two k (Nat.eq_of_mul_eq_mul_left hp.pos hsk)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Exhaustive search: no odd number below `1000` is superperfect. -/
lemma no_odd_superperfect_below_1000 {n : ℕ} (hlt : n < 1000) (hn : Odd n) :
    ¬ Superperfect n := by
  have key : ∀ m < 1000, m % 2 = 1 →
      (∑ d ∈ (∑ e ∈ (m : ℕ).divisors, e).divisors, d) ≠ 2 * m := by
    decide +kernel
  have hn' : n % 2 = 1 := Nat.odd_iff.mp hn
  intro hs
  rw [Superperfect, sig_eq_sum, sig_eq_sum] at hs
  exact key n hlt hn' hs

/-- **Odd superperfect numbers: a conditional reduction.**

Whether an odd superperfect number exists is an open problem; no unconditional
existence proof is given here.  What is proved is a reduction: an odd superperfect
number exists if and only if one exists that is larger than `1000`, is not prime,
and whose sum-of-divisors `σ(n) = 2 ^ a * k` (with `k` odd) satisfies
`(2 ^ (a+1) - 1) * σ(k) = 2 * n`. -/
theorem OddSuperperfectExists :
    (∃ n, Odd n ∧ Superperfect n) ↔
      ∃ n, Odd n ∧ Superperfect n ∧ 1000 < n ∧ ¬ n.Prime ∧
        ∃ a k, Odd k ∧ sig n = 2 ^ a * k ∧ (2 ^ (a + 1) - 1) * sig k = 2 * n := by
  constructor
  · rintro ⟨n, hn, hs⟩
    refine ⟨n, hn, hs, ?_, ?_, odd_superperfect_structure hn hs⟩
    · by_contra h
      push_neg at h
      have hpar : n % 2 = 1 := Nat.odd_iff.mp hn
      exact no_odd_superperfect_below_1000 (by omega) hn hs
    · intro hp
      exact not_superperfect_prime hp hn hs
  · rintro ⟨n, hn, hs, -⟩
    exact ⟨n, hn, hs⟩

end SuperperfectNumbers
end Brockian

