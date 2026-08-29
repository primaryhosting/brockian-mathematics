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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem six_unitary_perfect_iff_exists_new :
    (∃ S : Finset ℕ, S.card = 6 ∧ ∀ m ∈ S, IsUnitaryPerfect m) ↔
      ∃ n, IsUnitaryPerfect n ∧ n ∉ knownFive := by
  constructor
  · rintro ⟨S, hcard, hS⟩
    by_contra hcon
    push_neg at hcon
    have hsub : S ⊆ knownFive := fun m hm => hcon m (hS m hm)
    have hle := Finset.card_le_card hsub
    rw [hcard, card_knownFive] at hle
    omega
  · rintro ⟨n, hn, hnot⟩
    refine ⟨insert n knownFive, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hnot, card_knownFive]
    · intro m hm
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact hn
      · exact isUnitaryPerfect_of_mem_knownFive hm

/-! ## Main conditional theorem -/

/--
**Sixth unitary perfect number (conditional reduction).**

Whether a sixth unitary perfect number exists is an open problem: only the five numbers
`6, 60, 90, 87360, 146361946186458562560000` are known, and it is not known whether a further
one exists.

The theorem below is a Lean-checked reduction: *if* there is any unitary perfect number larger
than the largest currently known one, *then* there are at least six unitary perfect numbers,
exhibited as a six-element finite set all of whose members are unitary perfect. The five known
values are verified here from scratch, via the multiplicativity of `σ*`.
-/
