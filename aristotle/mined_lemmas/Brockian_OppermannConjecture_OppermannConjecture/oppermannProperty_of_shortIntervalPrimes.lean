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
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Brockian.OppermannConjecture

/-- Oppermann's property for `n`: there is a prime strictly between `n(n-1)` and `n²`,
and a prime strictly between `n²` and `n(n+1)`. -/

lemma oppermannProperty_of_shortIntervalPrimes (X : ℕ) (hX : ShortIntervalPrimes X) (n : ℕ)
    (h2 : 2 ≤ n) (hn : X ≤ n) : OppermannProperty n := by
  have hnn : n + n ≤ n * n := by nlinarith
  constructor
  · obtain ⟨p, hp, h1, h2⟩ := hX (n * n - n) (le_trans hn (by omega))
    refine ⟨p, hp, h1, ?_⟩
    have hs : Nat.sqrt (n * n - n) ≤ n :=
      le_of_le_of_eq (Nat.sqrt_le_sqrt (Nat.sub_le _ _)) (Nat.sqrt_eq n)
    omega
  · obtain ⟨p, hp, h1, h2⟩ := hX (n * n) (le_trans hn (by omega))
    rw [Nat.sqrt_eq] at h2
    exact ⟨p, hp, h1, h2⟩

/-- **Oppermann's conjecture, conditionally on a short-interval prime hypothesis.**

If there is a threshold `X ≤ 501` beyond which every interval `(x, x + √x)` contains a prime,
then Oppermann's conjecture holds in full: for every `n ≥ 2` there is a prime strictly between
`n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`.

The range `n ≤ 500` is verified unconditionally (`oppermannProperty_of_le_500`); the hypothesis
is used only for `n > 500`. -/
