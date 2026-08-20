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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any doc-comment command, so the header above is written as a
-- plain block comment; its text is verbatim as requested.)

import Mathlib

/-!
The main result of this file is `Brockian.PracticalNumbers.PracticalTwinInfinitude`:
there are infinitely many `n` such that both `n` and `n + 2` are practical numbers.

The proof is completely explicit. We show that for every `t`, the pair
`(2 * (3 ^ 2 ^ t - 1), 2 * 3 ^ 2 ^ t)` is a pair of practical numbers differing by `2`
(e.g. `(4, 6)`, `(16, 18)`, `(160, 162)`, `(13120, 13122)`, ...).

The engine is the classical closure property `IsPractical.mul`: if `n` is practical and
`0 < m ≤ σ n + 1`, then `n * m` is practical. Iterating it along the factorisation
`3 ^ 2 ^ t - 1 = 2 * (3 ^ 2 ^ 0 + 1) * (3 ^ 2 ^ 1 + 1) * ⋯ * (3 ^ 2 ^ (t-1) + 1)`
(realised here as a simple induction on `t`) yields practicality of `2 * (3 ^ 2 ^ t - 1)`,
while practicality of `2 * 3 ^ a` is an even simpler induction.
-/

namespace Brockian.PracticalNumbers

open Finset

/-- `n` is a *practical number* if it is positive and every `k ≤ n` can be written as a sum of
distinct divisors of `n`. -/

theorem divisor_le_sum_smaller {n : ℕ} (hn : IsPractical n) {d : ℕ} (hd : d ∈ n.divisors) :
    d ≤ 1 + ∑ e ∈ n.divisors.filter (· < d), e := by
  by_contra hc
  push_neg at hc
  set s := ∑ e ∈ n.divisors.filter (· < d), e with hs
  have hdn : d ≤ n := Nat.le_of_dvd hn.1 (Nat.dvd_of_mem_divisors hd)
  have hle : s + 1 ≤ n := by omega
  obtain ⟨T, hT, hTsum⟩ := hn.2 (s + 1) hle
  have hTlt : ∀ x ∈ T, x < d := by
    intro x hx
    have : x ≤ s + 1 :=
      hTsum ▸ Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    omega
  have hTsub : T ⊆ n.divisors.filter (· < d) := fun x hx =>
    Finset.mem_filter.2 ⟨hT hx, hTlt x hx⟩
  have h2 : ∑ x ∈ T, x ≤ s := Finset.sum_le_sum_of_subset hTsub
  omega

/-- For a practical number `n`, every `k` up to `σ n` is a sum of distinct divisors of `n`. -/
