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

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

A natural number `n` is *weird* (`Nat.Weird`, from Mathlib) when it is abundant
(the sum of its proper divisors exceeds `n`) but not pseudoperfect (no subset of its
proper divisors sums to `n`).  Whether an **odd** weird number exists is a well-known
open problem, so the unconditional statement `∃ n, Odd n ∧ Nat.Weird n` is not proved
here.  Instead this file contains:

* `Brockian.WeirdNumbers.abundance`: the abundance `σ(n) - 2n` of `n`.
* `Brockian.WeirdNumbers.pseudoperfect_iff_exists_sum_eq_abundance`: for an abundant `n`,
  `n` is pseudoperfect iff some subset of its proper divisors sums to the *abundance* of
  `n` (complementation of subsets).  This turns the subset-sum target `n` into the much
  smaller target `abundance n`.
* `Brockian.WeirdNumbers.OddWeirdExists`: an unconditional Lean-checked **reduction** of
  the open problem: an odd weird number exists **iff** there is an odd abundant number no
  subset of whose proper divisors sums to its abundance.
* `Brockian.WeirdNumbers.weird_of_abundance_small`: a practical sufficient criterion for
  weirdness (abundance different from `1` and smaller than every proper divisor `> 1`).
* `Brockian.WeirdNumbers.weird_seventy` / `exists_weird`: `70` is weird, so weird numbers
  do exist (unconditionally, by a finite kernel computation).
-/

open Finset

set_option maxRecDepth 40000

namespace Brockian.WeirdNumbers

/-- The *abundance* of `n`, i.e. `σ(n) - 2n`, written as the excess of the sum of the
proper divisors of `n` over `n` itself (truncated subtraction). -/

theorem weird_of_abundance_small {n : ℕ} (hn : 0 < n) (h : n.Abundant)
    (h1 : abundance n ≠ 1)
    (hlt : ∀ d ∈ n.properDivisors, d = 1 ∨ abundance n < d) : n.Weird := by
  rw [weird_iff_abundant_and_abundance_not_subset_sum hn]
  refine ⟨h, ?_⟩
  intro t ht hsum
  have habpos := abundance_pos h
  by_cases hex : ∃ d ∈ t, d ≠ 1
  · obtain ⟨d, hdt, hd1⟩ := hex
    have hdle : d ≤ ∑ i ∈ t, i :=
      Finset.single_le_sum (f := fun i => i) (by intros; positivity) hdt
    rcases hlt d (ht hdt) with h' | h'
    · exact hd1 h'
    · omega
  · push_neg at hex
    have hsub : t ⊆ {1} := fun x hx => by simp [hex x hx]
    have hcard : t.card ≤ 1 := by simpa using Finset.card_le_card hsub
    have hle : ∑ i ∈ t, i ≤ 1 := by
      calc ∑ i ∈ t, i = ∑ _i ∈ t, 1 := Finset.sum_congr rfl fun x hx => hex x hx
        _ = t.card := by simp
        _ ≤ 1 := hcard
    omega

/-- `70` is a weird number (the smallest one). -/
