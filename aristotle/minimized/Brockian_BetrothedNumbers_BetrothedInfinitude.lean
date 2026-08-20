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

open Finset

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
they are distinct positive integers with
`σ₁ m = σ₁ n = m + n + 1`, i.e. each is the sum of the *proper* divisors
(excluding `1` and the number itself) of the other. -/

def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- The set of betrothed pairs. -/

def betrothedSet : Set (ℕ × ℕ) := {p | IsBetrothedPair p.1 p.2}

/-- The smallest betrothed pair. -/

theorem eq_of_fst_eq {m n m' n' : ℕ} (h : IsBetrothedPair m n) (h' : IsBetrothedPair m' n')
    (hm : m = m') : n = n' := by
  obtain ⟨-, -, -, h1, -⟩ := h
  obtain ⟨-, -, -, h1', -⟩ := h'
  subst hm
  omega

/-- Taking the first component is injective on the set of betrothed pairs. -/

theorem injOn_fst_betrothedSet : Set.InjOn Prod.fst betrothedSet := by
  rintro ⟨m, n⟩ hp ⟨m', n'⟩ hq hmm
  simp only [betrothedSet, Set.mem_setOf_eq] at hp hq
  simp only at hmm
  exact Prod.ext hmm (eq_of_fst_eq hp hq hmm)

/-!
## Main statement

Whether there are infinitely many betrothed (quasi-amicable) pairs is an open
problem.  What we prove here is the exact *reduction* of infinitude to
unboundedness: the set of betrothed pairs is infinite if and only if the first
members of betrothed pairs are unbounded.  Both directions are unconditional
theorems; the conjecture itself is the (unproved) right-hand side.
-/

/-- **Betrothed infinitude, as a reduction.**
The set of betrothed pairs is infinite iff for every bound `N` there is a
betrothed pair `(m, n)` with `N < m`. -/

theorem BetrothedInfinitude :
    betrothedSet.Infinite ↔ ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothedPair m n := by
  constructor
  · intro hinf N
    have himg : (Prod.fst '' betrothedSet).Infinite := hinf.image injOn_fst_betrothedSet
    obtain ⟨m, hm, hNm⟩ := himg.exists_gt N
    obtain ⟨⟨m', n⟩, hmem, rfl⟩ := hm
    exact ⟨m', n, hNm, hmem⟩
  · intro h
    refine Set.Infinite.of_image Prod.fst ?_
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨m, n, hNm, hmn⟩ := h N
    have : m ≤ N := hN ⟨(m, n), hmn, rfl⟩
    omega

/-- The set of betrothed pairs is nonempty. -/
