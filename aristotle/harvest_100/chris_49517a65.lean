/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: the header is written as a plain block comment rather than a module docstring,
because Lean requires `import` commands to precede any docstring.)
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

namespace Brockian
namespace BetrothedNumbers

/-- `sigmaOne n` is the sum of the divisors of `n`, i.e. `σ₁ n`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A pair of *betrothed* (quasi-amicable) numbers: two distinct positive integers, each of
which is the sum of the nontrivial divisors (those excluding `1` and the number itself) of the
other; equivalently `σ(m) = σ(n) = m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- Geometric-sum bound: `(1 + p + ⋯ + p ^ a) * (p - 1) ≤ p ^ (a + 1)`. -/
lemma geom_sum_mul_pred_le (p a : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) ≤ p ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, add_mul]
    calc (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + p ^ (a + 1) * (p - 1)
        ≤ p ^ (a + 1) + p ^ (a + 1) * (p - 1) := by gcongr
      _ = p ^ (a + 1) * (1 + (p - 1)) := by ring
      _ = p ^ (a + 1 + 1) := by rw [show 1 + (p - 1) = p from by omega]; ring

/-- The abundancy bound coming from the Euler product:
`σ(N) * ∏_{p ∣ N} (p - 1) ≤ N * ∏_{p ∣ N} p`, i.e. `σ(N)/N ≤ ∏_{p ∣ N} p/(p-1)`. -/
lemma sigmaOne_mul_prod_pred_le (N : ℕ) (hN : N ≠ 0) :
    sigmaOne N * ∏ p ∈ N.primeFactors, (p - 1) ≤ N * ∏ p ∈ N.primeFactors, p := by
  have hs : sigmaOne N
      = ∏ p ∈ N.primeFactors, ∑ k ∈ Finset.range (N.factorization p + 1), p ^ k :=
    Nat.sum_divisors hN
  have hNfac : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by
    rw [← Nat.support_factorization]; exact Nat.factorization_prod_pow_eq_self hN
  have hrw : N * ∏ p ∈ N.primeFactors, p
      = (∏ p ∈ N.primeFactors, p ^ N.factorization p) * ∏ p ∈ N.primeFactors, p := by
    rw [hNfac]
  rw [hs, hrw, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' ?_
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  calc (∑ k ∈ Finset.range (N.factorization p + 1), p ^ k) * (p - 1)
      ≤ p ^ (N.factorization p + 1) := geom_sum_mul_pred_le p _ hpp.one_lt.le
    _ = p ^ N.factorization p * p := by ring

/-- For three primes of sizes at least `2`, `3` and `5`, `a * b * c ≤ 4 * (a-1)(b-1)(c-1)`. -/
lemma three_primes_prod_le {a b c : ℕ} (ha : 2 ≤ a) (hb : 3 ≤ b) (hc : 5 ≤ c) :
    a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
  zify [show 1 ≤ a from by omega, show 1 ≤ b from by omega, show 1 ≤ c from by omega]
  nlinarith [mul_nonneg (sub_nonneg.2 (show (2:ℤ) ≤ a by exact_mod_cast ha))
      (sub_nonneg.2 (show (3:ℤ) ≤ b by exact_mod_cast hb)),
    mul_pos (show (0:ℤ) < a by positivity) (show (0:ℤ) < b by positivity),
    show (5:ℤ) ≤ c by exact_mod_cast hc]

/-- A finite set of at most three primes satisfies `∏ p ≤ 4 * ∏ (p - 1)`; the extremal case is
`{2, 3, 5}`, where `30 ≤ 32`. Equivalently `∏ p/(p-1) ≤ 15/4 < 4`. -/
lemma prod_le_four_mul_prod_pred (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    ∏ p ∈ S, p ≤ 4 * ∏ p ∈ S, (p - 1) := by
  have hsplit : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hsplit with h | h | h | h
  · rw [Finset.card_eq_zero] at h
    subst h
    simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have ha := (hS a (by simp)).two_le
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have ha := (hS a (by simp)).two_le
    have hb := (hS b (by simp)).two_le
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    zify [show 1 ≤ a from by omega, show 1 ≤ b from by omega]
    nlinarith [show (2:ℤ) ≤ a by exact_mod_cast ha, show (2:ℤ) ≤ b by exact_mod_cast hb]
  · -- Three distinct primes: one of them is at least `5`, another at least `3`.
    obtain ⟨c, hcS, hc5⟩ : ∃ c ∈ S, 5 ≤ c := by
      have hne : ((S.erase 2).erase 3).Nonempty := by
        rw [← Finset.card_pos]
        have h1 := Finset.pred_card_le_card_erase (s := S) (a := 2)
        have h2 := Finset.pred_card_le_card_erase (s := S.erase 2) (a := 3)
        omega
      obtain ⟨c, hc⟩ := hne
      have h3 : c ≠ 3 := Finset.ne_of_mem_erase hc
      have hc' := Finset.mem_of_mem_erase hc
      have h2 : c ≠ 2 := Finset.ne_of_mem_erase hc'
      have hcS : c ∈ S := Finset.mem_of_mem_erase hc'
      refine ⟨c, hcS, ?_⟩
      have hp := hS c hcS
      have h4 : c ≠ 4 := by rintro rfl; norm_num at hp
      have := hp.two_le
      omega
    obtain ⟨b, hbS, hbc, hb3⟩ : ∃ b ∈ S, b ≠ c ∧ 3 ≤ b := by
      have hne : ((S.erase c).erase 2).Nonempty := by
        rw [← Finset.card_pos]
        have h1 : (S.erase c).card = 2 := by rw [Finset.card_erase_of_mem hcS]; omega
        have h2 := Finset.pred_card_le_card_erase (s := S.erase c) (a := 2)
        omega
      obtain ⟨b, hb⟩ := hne
      have h2 : b ≠ 2 := Finset.ne_of_mem_erase hb
      have hb' := Finset.mem_of_mem_erase hb
      have hbc : b ≠ c := Finset.ne_of_mem_erase hb'
      have hbS : b ∈ S := Finset.mem_of_mem_erase hb'
      exact ⟨b, hbS, hbc, by have := (hS b hbS).two_le; omega⟩
    have hbe : b ∈ S.erase c := Finset.mem_erase.mpr ⟨hbc, hbS⟩
    obtain ⟨a, hTa⟩ : ∃ a, (S.erase c).erase b = {a} := by
      rw [← Finset.card_eq_one, Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem hcS]
      omega
    have haS : a ∈ S := by
      have hmem : a ∈ (S.erase c).erase b := by rw [hTa]; simp
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem)
    have ha2 := (hS a haS).two_le
    have e1 : ∀ f : ℕ → ℕ, ∏ p ∈ S, f p = f a * f b * f c := by
      intro f
      rw [← Finset.prod_erase_mul S f hcS, ← Finset.prod_erase_mul (S.erase c) f hbe, hTa,
        Finset.prod_singleton]
    rw [e1 (fun p => p), e1 (fun p => p - 1)]
    exact three_primes_prod_le ha2 hb3 hc5

/-- The abundancy inequality for a coprime betrothed pair: `σ(mn) = (m+n+1)^2 > 4mn`. -/
lemma sigmaOne_mul_gt (m n : ℕ) (h : Betrothed m n) (hco : Nat.Coprime m n) :
    4 * (m * n) < sigmaOne (m * n) := by
  obtain ⟨hm, hn, -, hsm, hsn⟩ := h
  have hmul : sigmaOne (m * n) = sigmaOne m * sigmaOne n := by
    simpa [sigmaOne] using Nat.Coprime.sum_divisors_mul hco
  rw [hmul, hsm, hsn]
  zify
  nlinarith [sq_nonneg ((m : ℤ) - n), show (1:ℤ) ≤ m by exact_mod_cast hm,
    show (1:ℤ) ≤ n by exact_mod_cast hn]

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed numbers, then `m * n`
has at least four distinct prime factors.

The proof combines multiplicativity of `σ` (giving `σ(mn) = (m+n+1)^2 > 4mn`) with the Euler
product bound `σ(N)/N ≤ ∏_{p ∣ N} p/(p-1)`: three or fewer distinct prime factors force
`∏ p/(p-1) ≤ 2 · (3/2) · (5/4) = 15/4 < 4`, a contradiction. -/
theorem coprime_pair_four_primeFactors {m n : ℕ} (h : Betrothed m n) (hco : Nat.Coprime m n) :
    4 ≤ (m * n).primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hm : 0 < m := h.1
  have hn : 0 < n := h.2.1
  have hN : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
  have hcard : (m * n).primeFactors.card ≤ 3 := by omega
  have hQ : ∏ p ∈ (m * n).primeFactors, p ≤ 4 * ∏ p ∈ (m * n).primeFactors, (p - 1) :=
    prod_le_four_mul_prod_pred _ (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have hP : 0 < ∏ p ∈ (m * n).primeFactors, (p - 1) :=
    Finset.prod_pos fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
  have hkey := sigmaOne_mul_prod_pred_le (m * n) hN
  have hgt := sigmaOne_mul_gt m n h hco
  have hchain :
      4 * (m * n) * ∏ p ∈ (m * n).primeFactors, (p - 1)
        < 4 * (m * n) * ∏ p ∈ (m * n).primeFactors, (p - 1) :=
    calc 4 * (m * n) * ∏ p ∈ (m * n).primeFactors, (p - 1)
        < sigmaOne (m * n) * ∏ p ∈ (m * n).primeFactors, (p - 1) := by
          exact (Nat.mul_lt_mul_right hP).mpr hgt
      _ ≤ (m * n) * ∏ p ∈ (m * n).primeFactors, p := hkey
      _ ≤ (m * n) * (4 * ∏ p ∈ (m * n).primeFactors, (p - 1)) := by
          exact Nat.mul_le_mul_left _ hQ
      _ = 4 * (m * n) * ∏ p ∈ (m * n).primeFactors, (p - 1) := by ring
  exact absurd hchain (lt_irrefl _)

end BetrothedNumbers
end Brockian

