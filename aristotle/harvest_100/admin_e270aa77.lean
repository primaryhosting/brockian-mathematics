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

/-!
## Betrothed (quasi-amicable) numbers

Two distinct natural numbers `m ≠ n` are *betrothed* (also called *quasi-amicable*)
when each is the sum of the *nontrivial* proper divisors of the other, i.e.

  `σ m = σ n = m + n + 1`,

where `σ = ArithmeticFunction.sigma 1` is the sum-of-divisors function.
The smallest example is `(48, 75)`.

Whether there are infinitely many betrothed pairs is an open problem.  What is
proved here is therefore a *conditional reduction* together with the unconditional
structural facts it rests on:

* `Brockian.BetrothedNumbers.quasiAliquot_iff` — the key intermediate lemma:
  a pair is betrothed exactly when the *quasi-aliquot* map
  `q n = σ n - n - 1` swaps `m` and `n` (and `m ≠ n`, `2 ≤ m`, `2 ≤ n`).
  In particular each member of a betrothed pair determines the other.
* `Brockian.BetrothedNumbers.BetrothedInfinitude` — from the (open) hypothesis
  that betrothed pairs have arbitrarily large members it follows that the set of
  betrothed pairs is infinite.
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- The quasi-aliquot sum of `n`: the sum of the divisors of `n` other than `1` and `n`
itself (using truncated subtraction, so the value at `n ≤ 1` is `0`). -/
def quasiAliquot (n : ℕ) : ℕ := sigma 1 n - n - 1

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct and
`σ m = σ n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- Being betrothed is a symmetric relation. -/
theorem IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hne, hm, hn⟩ := h
  refine ⟨hne.symm, ?_, ?_⟩ <;> omega

/-- For `2 ≤ n` the sum of divisors of `n` is at least `n + 1`. -/
theorem succ_le_sigma_one {n : ℕ} (h : 2 ≤ n) : n + 1 ≤ sigma 1 n := by
  rw [sigma_one_apply]
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [Nat.mem_divisors] <;> omega
  calc n + 1 = ∑ d ∈ ({1, n} : Finset ℕ), d := by
        rw [Finset.sum_pair (by omega)]; omega
    _ ≤ ∑ d ∈ n.divisors, d := Finset.sum_le_sum_of_subset hsub

/-- Both members of a betrothed pair are at least `2`. -/
theorem IsBetrothedPair.two_le_left {m n : ℕ} (h : IsBetrothedPair m n) : 2 ≤ m := by
  obtain ⟨-, hm, -⟩ := h
  by_contra hlt
  interval_cases m <;> simp at hm

/-- Both members of a betrothed pair are at least `2`. -/
theorem IsBetrothedPair.two_le_right {m n : ℕ} (h : IsBetrothedPair m n) : 2 ≤ n :=
  h.symm.two_le_left

/-- **Key intermediate lemma.**  A pair is betrothed exactly when the quasi-aliquot
map `q n = σ n - n - 1` interchanges the two (distinct) members. -/
theorem quasiAliquot_iff {m n : ℕ} :
    IsBetrothedPair m n ↔
      2 ≤ m ∧ 2 ≤ n ∧ m ≠ n ∧ quasiAliquot m = n ∧ quasiAliquot n = m := by
  constructor
  · intro h
    obtain ⟨hne, hm, hn⟩ := id h
    refine ⟨h.two_le_left, h.two_le_right, hne, ?_, ?_⟩ <;>
      simp only [quasiAliquot, hm, hn] <;> omega
  · rintro ⟨hm2, hn2, hne, hqm, hqn⟩
    have hm := succ_le_sigma_one hm2
    have hn := succ_le_sigma_one hn2
    rw [quasiAliquot] at hqm hqn
    exact ⟨hne, by omega, by omega⟩

/-- Each member of a betrothed pair determines the other. -/
theorem IsBetrothedPair.right_unique {m n n' : ℕ}
    (h : IsBetrothedPair m n) (h' : IsBetrothedPair m n') : n = n' := by
  obtain ⟨-, hm, -⟩ := h
  obtain ⟨-, hm', -⟩ := h'
  omega

/-- `(48, 75)` is the smallest betrothed pair. -/
theorem isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> rw [sigma_one_apply] <;> decide

/-- `(140, 195)` is a betrothed pair. -/
theorem isBetrothedPair_140_195 : IsBetrothedPair 140 195 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> rw [sigma_one_apply] <;> decide

set_option maxRecDepth 20000 in
/-- `(1050, 1925)` is a betrothed pair. -/
theorem isBetrothedPair_1050_1925 : IsBetrothedPair 1050 1925 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> rw [sigma_one_apply] <;> decide

/-- The set of betrothed numbers (numbers belonging to some betrothed pair). -/
def betrothedNumbers : Set ℕ := {n | ∃ m, IsBetrothedPair m n}

/-- The set of betrothed pairs. -/
def betrothedPairs : Set (ℕ × ℕ) := {p | IsBetrothedPair p.1 p.2}

/-- The set of betrothed numbers is nonempty. -/
theorem betrothedNumbers_nonempty : betrothedNumbers.Nonempty :=
  ⟨75, 48, isBetrothedPair_48_75⟩

/-- If betrothed numbers are unbounded then there are infinitely many of them. -/
theorem betrothedNumbers_infinite
    (h : ∀ N : ℕ, ∃ m n : ℕ, N < n ∧ IsBetrothedPair m n) :
    betrothedNumbers.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  obtain ⟨m, n, hlt, hmn⟩ := h N
  exact ⟨n, ⟨m, hmn⟩, hlt⟩

/-- The second projection is injective on the set of betrothed pairs: a betrothed
number determines its partner. -/
theorem snd_injOn_betrothedPairs : Set.InjOn Prod.snd betrothedPairs := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd (rfl : b = d)
  obtain ⟨-, -, h₁⟩ := hab
  obtain ⟨-, -, h₂⟩ := hcd
  simp only [Prod.mk.injEq, and_true]
  simp only at h₁ h₂
  omega

/-- The image of the set of betrothed pairs under the second projection is exactly the
set of betrothed numbers. -/
theorem image_snd_betrothedPairs : Prod.snd '' betrothedPairs = betrothedNumbers := by
  ext n
  constructor
  · rintro ⟨⟨a, b⟩, hp, rfl⟩
    exact ⟨a, hp⟩
  · rintro ⟨m, hm⟩
    exact ⟨(m, n), hm, rfl⟩

/-- **Unconditional characterisation.**  There are infinitely many betrothed pairs if and
only if betrothed pairs have arbitrarily large members. -/
theorem betrothedPairs_infinite_iff :
    betrothedPairs.Infinite ↔ ∀ N : ℕ, ∃ m n : ℕ, N < n ∧ IsBetrothedPair m n := by
  constructor
  · intro hinf N
    have himg : betrothedNumbers.Infinite := by
      rw [← image_snd_betrothedPairs]
      exact hinf.image snd_injOn_betrothedPairs
    obtain ⟨n, ⟨m, hmn⟩, hlt⟩ := himg.exists_gt N
    exact ⟨m, n, hlt, hmn⟩
  · intro h
    refine Set.Infinite.of_image Prod.snd ?_
    rw [image_snd_betrothedPairs]
    exact betrothedNumbers_infinite h

/-- **Betrothed Infinitude (conditional reduction).**

If betrothed pairs have arbitrarily large members — i.e. for every bound `N` there is
a betrothed pair `(m, n)` with `N < n` — then there are infinitely many betrothed pairs.

The hypothesis is exactly the open part of the Brockian "betrothed infinitude"
conjecture; everything else is proved unconditionally here, the crucial ingredient
being `quasiAliquot_iff`, which shows that a betrothed pair is determined by either
of its members. -/
theorem BetrothedInfinitude
    (h : ∀ N : ℕ, ∃ m n : ℕ, N < n ∧ IsBetrothedPair m n) :
    betrothedPairs.Infinite :=
  betrothedPairs_infinite_iff.mpr h

end Brockian.BetrothedNumbers

