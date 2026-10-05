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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* if its set of divisors can be split into
two parts with equal sums, i.e. there is a set `A` of divisors of `n` whose sum is exactly
half of `σ(n)`. -/

theorem zumkeller_mul_of_coprime {n k : ℕ} (hn : IsZumkeller n) (hk : 0 < k)
    (h : Nat.Coprime n k) : IsZumkeller (n * k) := by
  obtain ⟨hnpos, A, hA, hsum⟩ := hn
  have hinj : ∀ p ∈ A ×ˢ k.divisors, ∀ q ∈ A ×ˢ k.divisors,
      p.1 * p.2 = q.1 * q.2 → p = q := by
    rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq heq
    simp only [Finset.mem_product] at hp hq
    have hp1 : p1 ∣ n := (Nat.mem_divisors.mp (hA hp.1)).1
    have hq1 : q1 ∣ n := (Nat.mem_divisors.mp (hA hq.1)).1
    have hp2 : p2 ∣ k := (Nat.mem_divisors.mp hp.2).1
    have hq2 : q2 ∣ k := (Nat.mem_divisors.mp hq.2).1
    have hc1 : Nat.Coprime p1 q2 := (Nat.Coprime.coprime_dvd_left hp1 h).coprime_dvd_right hq2
    have hc2 : Nat.Coprime q1 p2 := (Nat.Coprime.coprime_dvd_left hq1 h).coprime_dvd_right hp2
    simp only at heq
    have h1 : p1 ∣ q1 := hc1.dvd_of_dvd_mul_right ⟨p2, heq.symm⟩
    have h2 : q1 ∣ p1 := hc2.dvd_of_dvd_mul_right ⟨q2, heq⟩
    have hEq1 : p1 = q1 := Nat.dvd_antisymm h1 h2
    subst hEq1
    have hp1pos : 0 < p1 := Nat.pos_of_dvd_of_pos hp1 hnpos
    have h3 : p2 = q2 := by
      have h4 := heq
      rw [Nat.mul_left_cancel_iff hp1pos] at h4
      exact h4
    simp [h3]
  refine ⟨Nat.mul_pos hnpos hk, (A ×ˢ k.divisors).image (fun p => p.1 * p.2), ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_product] at hx
    obtain ⟨⟨p1, p2⟩, hp, rfl⟩ := hx
    rw [Nat.mem_divisors]
    exact ⟨mul_dvd_mul (Nat.mem_divisors.mp (hA hp.1)).1 (Nat.mem_divisors.mp hp.2).1,
      Nat.mul_ne_zero hnpos.ne' hk.ne'⟩
  · rw [Finset.sum_image hinj, Finset.sum_product]
    have h4 : ∑ x ∈ A, ∑ y ∈ k.divisors, x * y = (∑ x ∈ A, x) * ∑ y ∈ k.divisors, y := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
    rw [h4, ← mul_assoc, hsum, Nat.Coprime.sum_divisors_mul h]

/-- Twice the geometric sum of powers of `3`. -/
