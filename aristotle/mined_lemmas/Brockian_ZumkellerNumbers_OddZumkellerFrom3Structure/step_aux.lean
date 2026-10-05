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

lemma step_aux {b : ℕ} {T A : Finset ℕ} (hT : ∀ x ∈ T, x ∣ 35)
    (hA : A ⊆ (3 ^ b * 35 : ℕ).divisors) :
    (T ∪ A.image (fun d => 3 * d)) ⊆ (3 ^ (b + 1) * 35 : ℕ).divisors ∧
      (∑ d ∈ (T ∪ A.image (fun d => 3 * d)), (d : ℤ))
        = (∑ d ∈ T, (d : ℤ)) + 3 * ∑ d ∈ A, (d : ℤ) := by
  have hpos : (3 ^ (b + 1) * 35 : ℕ) ≠ 0 := by positivity
  have hdisj : Disjoint T (A.image (fun d => 3 * d)) := by
    rw [Finset.disjoint_right]
    rintro x hx hxT
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have h35 : (3 * d) ∣ 35 := hT _ hxT
    have h3 : (3 : ℕ) ∣ 35 := dvd_trans ⟨d, rfl⟩ h35
    norm_num at h3
  constructor
  · intro x hx
    rw [Finset.mem_union] at hx
    rw [Nat.mem_divisors]
    refine ⟨?_, hpos⟩
    rcases hx with hx | hx
    · exact dvd_trans (hT _ hx) ⟨3 ^ (b + 1), by ring⟩
    · simp only [Finset.mem_image] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      obtain ⟨c, hc⟩ := (Nat.mem_divisors.mp (hA hd)).1
      refine ⟨c, ?_⟩
      calc 3 ^ (b + 1) * 35 = 3 * (3 ^ b * 35) := by ring
        _ = 3 * (d * c) := by rw [hc]
        _ = 3 * d * c := by ring
  · rw [Finset.sum_union hdisj,
      Finset.sum_image
        (by intro x _ y _ h; simpa using h : ∀ x ∈ A, ∀ y ∈ A, 3 * x = 3 * y → x = y)]
    push_cast
    rw [Finset.mul_sum]

/-- Key lemma: for `b ≥ 3`, every integer within `12` of half the sum of the divisors of
`3 ^ b * 35` is realised as the sum of a set of divisors of `3 ^ b * 35`. -/
