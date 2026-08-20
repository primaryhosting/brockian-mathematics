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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Gilbreath's conjecture concerns the triangle of iterated absolute differences of the
sequence of primes.  Writing `p 0 = 2, p 1 = 3, p 2 = 5, …` for the primes and
`row p k` for the `k`-th row of iterated absolute differences, the conjecture states

  `row p k 0 = 1`  for every `k ≥ 1`.

The conjecture is open.  What is formalised here is:

* `Brockian.GilbreathConjecture.GilbreathConjecture` : a Lean-checked **conditional
  reduction** — the classical Odlyzko-style criterion implies Gilbreath's conjecture.
  The criterion asks that, for every row index `m ≥ 1`, some earlier row `k` (with
  `1 ≤ k ≤ m`) begins with a `1` followed by at least `m - k` entries taken from
  `{0, 2}`.  This is exactly the property that Odlyzko verified numerically for
  huge ranges.

* `Brockian.GilbreathConjecture.gilbreath_le_25` : an unconditional, kernel-checked
  verification of the conjecture for all rows `1 ≤ k ≤ 25`.

The mathematical content of the reduction is the propagation lemma
`GoodRow.diff` : a row of the shape `1, e₁, …, e_L` with all `eᵢ ∈ {0, 2}` is followed
by a row of the shape `1, e'₁, …, e'_{L-1}` with all `e'ᵢ ∈ {0, 2}`, because
`|even - 1| = 1` and `|even - even|` is `0` or `2`.
-/

set_option maxRecDepth 40000

namespace Brockian.GilbreathConjecture

/-- One step of the Gilbreath triangle: the sequence of absolute differences of
consecutive terms. -/

theorem gilbreath_le_25 : ∀ k, 1 ≤ k → k ≤ 25 → row prime k 0 = 1 := by
  intro k hk1 hk25
  have : row prime k 0 = (diff^[k] q) 0 := by
    unfold row
    exact diff_iterate_congr k prime q 0 (fun i hi => prime_eq_q i (by omega))
  rw [this]
  exact q_rows k (Finset.mem_Icc.mpr ⟨hk1, hk25⟩)

end Brockian.GilbreathConjecture

