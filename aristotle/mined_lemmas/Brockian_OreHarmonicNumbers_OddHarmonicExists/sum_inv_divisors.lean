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
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.OreHarmonicNumbers

/-- The harmonic mean of the (positive) divisors of `n`:
`τ(n) / ∑_{d ∣ n} 1/d`. -/

theorem sum_inv_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (1 : ℚ) / d = (∑ d ∈ n.divisors, (d : ℚ)) / n := by
  rw [← Nat.sum_div_divisors n (fun d => (1 : ℚ) / d), Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Nat.mem_divisors] at hd
  obtain ⟨⟨c, rfl⟩, hne⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hne)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hne)
  rw [Nat.mul_div_cancel_left _ hd0]
  have : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc0.ne'
  have : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  push_cast
  field_simp

/-- Closed form for the harmonic mean of the divisors: `n · τ(n) / σ(n)`. -/
