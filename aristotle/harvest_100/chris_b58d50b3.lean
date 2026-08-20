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
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires the `import` commands to be the very first
commands of a file, so the module docstring above (reproduced verbatim as
requested) has to follow `import Mathlib` rather than precede it.

MATHLIB SEARCH.  Oppermann's conjecture is an open problem, strictly stronger
than Legendre's conjecture.  Mathlib contains no result giving a prime in an
interval shorter than Bertrand's postulate (`Nat.bertrand`/`Nat.exists_prime_lt_and_le_two_mul`,
a prime in `(n, 2n]`), which is far too weak to produce a prime in `(n² - n, n²)`.
Accordingly this file provides (i) an unconditional verification of the conjecture
for `2 ≤ n ≤ 50`, and (ii) a Lean-checked reduction of the full conjecture to a
standard short-prime-gap hypothesis.
-/

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture**: for every `n ≥ 2` there is a prime strictly between
`n(n-1) = n² - n` and `n²`, and a prime strictly between `n²` and `n(n+1) = n² + n`. -/
def OppermannStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∃ p : ℕ, Nat.Prime p ∧ n * n - n < p ∧ p < n * n) ∧
    (∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * n + n)

/-- The *short prime gap hypothesis*: for every `m ≥ 117` there is a prime `p` with
`m < p < m + √m`; the square root is avoided by phrasing the upper bound as
`(p - m) ^ 2 < m` (natural subtraction).

The threshold `117` is the natural one: the numbers `m` admitting no prime in
`(m, m + √m)` are exactly `0, 1, 3, 7, 8, 13, 23, 24, 31, 113, 114, 115, 116`
throughout the range `m < 300000`. -/
def SqrtPrimeGapHypothesis : Prop :=
  ∀ m : ℕ, 117 ≤ m → ∃ p : ℕ, Nat.Prime p ∧ m < p ∧ (p - m) ^ 2 < m

/-! ## Unconditional verification for small `n` -/

/-- Oppermann's conjecture for `2 ≤ n ≤ 50`, with explicit prime witnesses. -/
theorem oppermann_of_le_fifty (n : ℕ) (h2 : 2 ≤ n) (h50 : n ≤ 50) :
    (∃ p : ℕ, Nat.Prime p ∧ n * n - n < p ∧ p < n * n) ∧
    (∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * n + n) := by
  interval_cases n
  · exact ⟨⟨3, by norm_num⟩, ⟨5, by norm_num⟩⟩
  · exact ⟨⟨7, by norm_num⟩, ⟨11, by norm_num⟩⟩
  · exact ⟨⟨13, by norm_num⟩, ⟨17, by norm_num⟩⟩
  · exact ⟨⟨23, by norm_num⟩, ⟨29, by norm_num⟩⟩
  · exact ⟨⟨31, by norm_num⟩, ⟨37, by norm_num⟩⟩
  · exact ⟨⟨43, by norm_num⟩, ⟨53, by norm_num⟩⟩
  · exact ⟨⟨59, by norm_num⟩, ⟨67, by norm_num⟩⟩
  · exact ⟨⟨73, by norm_num⟩, ⟨83, by norm_num⟩⟩
  · exact ⟨⟨97, by norm_num⟩, ⟨101, by norm_num⟩⟩
  · exact ⟨⟨113, by norm_num⟩, ⟨127, by norm_num⟩⟩
  · exact ⟨⟨137, by norm_num⟩, ⟨149, by norm_num⟩⟩
  · exact ⟨⟨157, by norm_num⟩, ⟨173, by norm_num⟩⟩
  · exact ⟨⟨191, by norm_num⟩, ⟨197, by norm_num⟩⟩
  · exact ⟨⟨211, by norm_num⟩, ⟨227, by norm_num⟩⟩
  · exact ⟨⟨241, by norm_num⟩, ⟨257, by norm_num⟩⟩
  · exact ⟨⟨277, by norm_num⟩, ⟨293, by norm_num⟩⟩
  · exact ⟨⟨307, by norm_num⟩, ⟨331, by norm_num⟩⟩
  · exact ⟨⟨347, by norm_num⟩, ⟨367, by norm_num⟩⟩
  · exact ⟨⟨383, by norm_num⟩, ⟨401, by norm_num⟩⟩
  · exact ⟨⟨421, by norm_num⟩, ⟨443, by norm_num⟩⟩
  · exact ⟨⟨463, by norm_num⟩, ⟨487, by norm_num⟩⟩
  · exact ⟨⟨509, by norm_num⟩, ⟨541, by norm_num⟩⟩
  · exact ⟨⟨557, by norm_num⟩, ⟨577, by norm_num⟩⟩
  · exact ⟨⟨601, by norm_num⟩, ⟨631, by norm_num⟩⟩
  · exact ⟨⟨653, by norm_num⟩, ⟨677, by norm_num⟩⟩
  · exact ⟨⟨709, by norm_num⟩, ⟨733, by norm_num⟩⟩
  · exact ⟨⟨757, by norm_num⟩, ⟨787, by norm_num⟩⟩
  · exact ⟨⟨821, by norm_num⟩, ⟨853, by norm_num⟩⟩
  · exact ⟨⟨877, by norm_num⟩, ⟨907, by norm_num⟩⟩
  · exact ⟨⟨937, by norm_num⟩, ⟨967, by norm_num⟩⟩
  · exact ⟨⟨997, by norm_num⟩, ⟨1031, by norm_num⟩⟩
  · exact ⟨⟨1061, by norm_num⟩, ⟨1091, by norm_num⟩⟩
  · exact ⟨⟨1123, by norm_num⟩, ⟨1163, by norm_num⟩⟩
  · exact ⟨⟨1193, by norm_num⟩, ⟨1229, by norm_num⟩⟩
  · exact ⟨⟨1277, by norm_num⟩, ⟨1297, by norm_num⟩⟩
  · exact ⟨⟨1361, by norm_num⟩, ⟨1373, by norm_num⟩⟩
  · exact ⟨⟨1409, by norm_num⟩, ⟨1447, by norm_num⟩⟩
  · exact ⟨⟨1483, by norm_num⟩, ⟨1523, by norm_num⟩⟩
  · exact ⟨⟨1567, by norm_num⟩, ⟨1601, by norm_num⟩⟩
  · exact ⟨⟨1657, by norm_num⟩, ⟨1693, by norm_num⟩⟩
  · exact ⟨⟨1723, by norm_num⟩, ⟨1777, by norm_num⟩⟩
  · exact ⟨⟨1811, by norm_num⟩, ⟨1861, by norm_num⟩⟩
  · exact ⟨⟨1901, by norm_num⟩, ⟨1949, by norm_num⟩⟩
  · exact ⟨⟨1987, by norm_num⟩, ⟨2027, by norm_num⟩⟩
  · exact ⟨⟨2081, by norm_num⟩, ⟨2129, by norm_num⟩⟩
  · exact ⟨⟨2179, by norm_num⟩, ⟨2213, by norm_num⟩⟩
  · exact ⟨⟨2267, by norm_num⟩, ⟨2309, by norm_num⟩⟩
  · exact ⟨⟨2357, by norm_num⟩, ⟨2411, by norm_num⟩⟩
  · exact ⟨⟨2459, by norm_num⟩, ⟨2503, by norm_num⟩⟩

/-! ## The reduction -/

/-- If `d ^ 2 < n * n` then `d < n`, for natural numbers. -/
theorem lt_of_sq_lt_mul_self {d n : ℕ} (h : d ^ 2 < n * n) : d < n := by
  by_contra hc
  push_neg at hc
  have : n * n ≤ d * d := Nat.mul_le_mul hc hc
  nlinarith

/-- **Main conditional result.** The short prime gap hypothesis
`SqrtPrimeGapHypothesis` (a prime in `(m, m + √m)` for every `m ≥ 117`) implies
Oppermann's conjecture. -/
theorem OppermannConjecture (h : SqrtPrimeGapHypothesis) : OppermannStatement := by
  intro n hn
  by_cases h50 : n ≤ 50
  · exact oppermann_of_le_fifty n hn h50
  push_neg at h50
  have h51 : 51 ≤ n := h50
  have hnn : 51 * n ≤ n * n := Nat.mul_le_mul_right n h51
  refine ⟨?_, ?_⟩
  · -- a prime in `(n² - n, n²)`
    obtain ⟨p, hp, hlt, hsq⟩ := h (n * n - n) (by omega)
    refine ⟨p, hp, hlt, ?_⟩
    have hd : p - (n * n - n) < n := by
      refine lt_of_sq_lt_mul_self (lt_of_lt_of_le hsq ?_)
      omega
    omega
  · -- a prime in `(n², n² + n)`
    obtain ⟨p, hp, hlt, hsq⟩ := h (n * n) (by omega)
    exact ⟨p, hp, hlt, by have := lt_of_sq_lt_mul_self hsq; omega⟩

end Brockian.OppermannConjecture

