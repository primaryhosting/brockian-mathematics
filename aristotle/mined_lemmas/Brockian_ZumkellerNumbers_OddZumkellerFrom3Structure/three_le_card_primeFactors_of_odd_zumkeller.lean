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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* when its set of divisors can be split into
two parts with equal sums, i.e. there is `S ⊆ n.divisors` whose sum is half of `σ₁ n`. -/

theorem three_le_card_primeFactors_of_odd_zumkeller {n : ℕ} (hodd : Odd n)
    (h : IsZumkeller n) : 3 ≤ n.primeFactors.card := by
  have hz := two_mul_le_sigma_of_isZumkeller h
  obtain ⟨hn, -⟩ := h
  by_contra hc
  push_neg at hc
  have hcard : n.primeFactors.card ≤ 2 := by omega
  rw [Nat.odd_iff] at hodd
  have hs : ∀ p ∈ n.primeFactors, p.Prime ∧ Odd p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hpp, ?_⟩
    rcases hpp.eq_two_or_odd' with rfl | h'
    · omega
    · exact h'
  have h1 := sigma_mul_prod_sub_one_le n hn
  have h2 := prod_lt_two_mul_prod_sub_one hs hcard
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    obtain ⟨hpp, hop⟩ := hs p hp
    have h2le := hpp.two_le
    have hne : p ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hop
    omega
  have key : (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
      < (2 * n) * ∏ p ∈ n.primeFactors, (p - 1) :=
    calc (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
        ≤ n * ∏ p ∈ n.primeFactors, p := h1
      _ < n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) := by gcongr
      _ = (2 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  have := Nat.lt_of_mul_lt_mul_right key
  omega

/-- Zumkeller numbers are stable under multiplication by a coprime factor. -/
