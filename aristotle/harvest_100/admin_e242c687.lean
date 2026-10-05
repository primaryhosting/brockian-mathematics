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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d` (with the convention `σ₁ 0 = 0`). -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct and each one's
sum of divisors equals `m + n + 1`, i.e. the sum of the proper divisors of each, excluding
`1`, is the other number. -/
def Betrothed (m n : ℕ) : Prop :=
  m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- The set of betrothed pairs. -/
def betrothedPairs : Set (ℕ × ℕ) := {p : ℕ × ℕ | Betrothed p.1 p.2}

/-- `(48, 75)` is a betrothed pair: `σ₁ 48 = σ₁ 75 = 124 = 48 + 75 + 1`. -/
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by decide, ?_, ?_⟩ <;> · unfold sigmaOne; decide

/-- `(140, 195)` is a betrothed pair: `σ₁ 140 = σ₁ 195 = 336 = 140 + 195 + 1`. -/
theorem betrothed_140_195 : Betrothed 140 195 := by
  refine ⟨by decide, ?_, ?_⟩ <;> · unfold sigmaOne; decide

/-- Being betrothed is a symmetric relation. -/
theorem betrothed_symm {m n : ℕ} (h : Betrothed m n) : Betrothed n m := by
  obtain ⟨hne, h1, h2⟩ := h
  exact ⟨hne.symm, by omega, by omega⟩

/-- The set of betrothed pairs is nonempty. -/
theorem betrothedPairs_nonempty : betrothedPairs.Nonempty :=
  ⟨(48, 75), betrothed_48_75⟩

/-- A number has at most one betrothed partner: the partner is determined by `σ₁`. -/
theorem betrothed_partner_unique {m n n' : ℕ} (h : Betrothed m n) (h' : Betrothed m n') :
    n = n' := by
  have h1 := h.2.1
  have h2 := h'.2.1
  omega

/-- Taking the first component is injective on the set of betrothed pairs. -/
theorem injOn_fst_betrothedPairs : Set.InjOn Prod.fst betrothedPairs := by
  rintro ⟨m, n⟩ hp ⟨m', n'⟩ hq (hmm : m = m')
  subst hmm
  simpa using betrothed_partner_unique hp hq

/--
**Betrothed Infinitude.**

There are infinitely many betrothed (quasi-amicable) pairs if and only if the first members
of such pairs are unbounded, i.e. for every `N` there is a betrothed pair whose first member
exceeds `N`.

(Whether either side actually holds is an open problem; this is the unconditional equivalence
of the two standard formulations of the conjecture.)
-/
theorem BetrothedInfinitude :
    (∀ N : ℕ, ∃ p : ℕ × ℕ, N < p.1 ∧ Betrothed p.1 p.2) ↔ betrothedPairs.Infinite := by
  constructor
  · intro h hfin
    obtain ⟨N, hN⟩ := (hfin.image Prod.fst).bddAbove
    obtain ⟨p, hp, hpB⟩ := h N
    have : p.1 ≤ N := hN ⟨p, hpB, rfl⟩
    omega
  · intro hinf N
    by_contra hcon
    push_neg at hcon
    refine hinf (Set.Finite.of_finite_image ?_ injOn_fst_betrothedPairs)
    refine Set.Finite.subset (Set.finite_Iic N) ?_
    rintro _ ⟨p, hp, rfl⟩
    exact le_of_not_gt fun hgt => hcon p hgt hp

/-- The set of *betrothed numbers*: numbers that belong to some betrothed pair. -/
def betrothedNumbers : Set ℕ := {m : ℕ | ∃ n, Betrothed m n}

theorem betrothedNumbers_eq_image : betrothedNumbers = Prod.fst '' betrothedPairs := by
  ext m
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨(m, n), hn, rfl⟩
  · rintro ⟨⟨m', n⟩, hp, rfl⟩
    exact ⟨n, hp⟩

/-- There are infinitely many betrothed numbers if and only if there are infinitely many
betrothed pairs. -/
theorem betrothedNumbers_infinite_iff : betrothedNumbers.Infinite ↔ betrothedPairs.Infinite := by
  rw [betrothedNumbers_eq_image]
  exact ⟨fun h => h.of_image _, fun h => h.image injOn_fst_betrothedPairs⟩

/-- Restatement of the target theorem in terms of betrothed *numbers*: the betrothed numbers
are infinite in number exactly when they are unbounded, exactly when there are infinitely
many betrothed pairs. -/
theorem betrothedNumbers_infinite_iff_unbounded :
    betrothedNumbers.Infinite ↔ ∀ N : ℕ, ∃ m ∈ betrothedNumbers, N < m := by
  rw [betrothedNumbers_infinite_iff, ← BetrothedInfinitude]
  constructor
  · rintro h N
    obtain ⟨p, hp1, hp2⟩ := h N
    exact ⟨p.1, ⟨p.2, hp2⟩, hp1⟩
  · rintro h N
    obtain ⟨m, ⟨n, hn⟩, hm⟩ := h N
    exact ⟨(m, n), hm, hn⟩

end Brockian.BetrothedNumbers

