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
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Brockian
namespace WeirdNumbers

/-- `n` is *semiperfect* (pseudoperfect) if `n` is positive and some set of proper divisors
of `n` sums to `n`. -/

theorem semiperfect_of_dvd {m n : ℕ} (hn : 0 < n) (hmn : m ∣ n) (hm : Semiperfect m) :
    Semiperfect n := by
  obtain ⟨hm0, S, hS, hsum⟩ := semiperfect_def.1 hm
  obtain ⟨k, rfl⟩ := hmn
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hn
    · exact hk
  refine semiperfect_def.2 ⟨hn, S.image (fun d => d * k), ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨d, hd, rfl⟩ := ht
    have hd' := hS hd
    rw [Nat.mem_properDivisors] at hd' ⊢
    exact ⟨mul_dvd_mul_right hd'.1 k, Nat.mul_lt_mul_of_lt_of_le hd'.2 le_rfl hk⟩
  · rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hk hab),
      ← Finset.sum_mul, hsum]

/-- A weird number has no semiperfect divisor. -/
