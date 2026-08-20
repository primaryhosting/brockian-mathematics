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
-- (Lean requires `import` to be the first command, so the header above is a plain block comment
-- and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.WeirdNumbers

/-! ## Setup

We use Mathlib's `Nat.Weird`: `n` is weird if it is *abundant*
(`n < ∑ i ∈ n.properDivisors, i`) but not *pseudoperfect* (no subset of its proper divisors
sums to `n`).

The statement "there exists an odd weird number" is an open problem, so the target
`OddWeirdExists` is formalised as a **conditional reduction**: from a verifiable criterion on a
single odd number we deduce the existence of an odd weird number.  The criterion involves the
*abundance* `∑ i ∈ n.properDivisors, i - n`, which is typically far smaller than `n`, so it is a
genuine reduction of the search problem.
-/

/-- The abundance of `n`: the sum of the proper divisors of `n` minus `n` (truncated
subtraction). -/

theorem Pseudoperfect.mul_of_dvd {m n : ℕ} (hm : m.Pseudoperfect) (hdvd : m ∣ n) (hmn : m < n) :
    n.Pseudoperfect := by
  obtain ⟨hm0, s, hs, hsum⟩ := hm
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 1 < k := by
    by_contra h
    interval_cases k <;> omega
  have hk0 : 0 < k := by omega
  refine ⟨by positivity, s.image (fun d => k * d), ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hd' := hs hd
    rw [Nat.mem_properDivisors] at hd' ⊢
    refine ⟨by rw [mul_comm m k]; exact mul_dvd_mul_left k hd'.1, ?_⟩
    calc k * d < k * m := (Nat.mul_lt_mul_left hk0).2 hd'.2
      _ = m * k := by ring
  · rw [Finset.sum_image (by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hk0 hab)]
    rw [← Finset.mul_sum, hsum]
    ring

/-- A weird number has no pseudoperfect proper divisor. -/
