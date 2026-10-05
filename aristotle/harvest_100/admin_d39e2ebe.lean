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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/
def IsSophieGermainPrime (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (2 * p + 1)

/-- A *safe prime* is a prime of the form `2 * p + 1` with `p` prime, i.e. the
larger member of a Sophie Germain pair. -/
def IsSafePrime (q : ℕ) : Prop := Nat.Prime q ∧ ∃ p : ℕ, q = 2 * p + 1 ∧ Nat.Prime p

/-! ### A convenient characterisation of infinitude for sets of naturals -/

/-- A set of naturals is infinite exactly when it contains arbitrarily large elements. -/
theorem infinite_iff_unbounded (S : Set ℕ) : S.Infinite ↔ ∀ N : ℕ, ∃ q ∈ S, N < q := by
  constructor
  · intro hS N
    obtain ⟨q, hqS, hq⟩ := (hS.diff (Set.finite_Iic N)).nonempty
    exact ⟨q, hqS, by simpa using hq⟩
  · intro h hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    obtain ⟨q, hq, hqN⟩ := h N
    exact absurd (hN hq) (by omega)

/-! ### Unconditional facts -/

/-- Small Sophie Germain primes. -/
theorem sophieGermain_examples :
    ∀ p ∈ [2, 3, 5, 11, 23, 29, 41, 53, 83, 89], IsSophieGermainPrime p := by
  intro p hp
  fin_cases hp <;> exact ⟨by norm_num, by norm_num⟩

/-- Every Sophie Germain prime larger than `3` is congruent to `5` modulo `6`. -/
theorem sophieGermain_mod_six {p : ℕ} (hp : IsSophieGermainPrime p) (h3 : 3 < p) :
    p % 6 = 5 := by
  obtain ⟨hp1, hp2⟩ := hp
  have h2 : ¬ (2 ∣ p) := by
    intro hd
    rcases (hp1.eq_one_or_self_of_dvd 2 hd) with h | h <;> omega
  have h3' : ¬ (3 ∣ p) := by
    intro hd
    rcases (hp1.eq_one_or_self_of_dvd 3 hd) with h | h <;> omega
  have hmod : p % 6 = 1 ∨ p % 6 = 5 := by
    rw [Nat.dvd_iff_mod_eq_zero] at h2 h3'
    omega
  rcases hmod with hm | hm
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, p = 6 * k + 1 := ⟨p / 6, by omega⟩
    have hdvd : 3 ∣ 2 * p + 1 := ⟨4 * k + 1, by omega⟩
    rcases (hp2.eq_one_or_self_of_dvd 3 hdvd) with h | h <;> omega
  · exact hm

/-- The Sophie Germain primes and the safe primes are in bijection via `p ↦ 2 * p + 1`,
so one family is infinite iff the other is. -/
theorem sophieGermain_infinite_iff_safe_infinite :
    {p : ℕ | IsSophieGermainPrime p}.Infinite ↔ {q : ℕ | IsSafePrime q}.Infinite := by
  rw [infinite_iff_unbounded, infinite_iff_unbounded]
  constructor
  · intro h N
    obtain ⟨p, hp, hpN⟩ := h N
    exact ⟨2 * p + 1, ⟨hp.2, p, rfl, hp.1⟩, by omega⟩
  · intro h N
    obtain ⟨q, hq, hqN⟩ := h (2 * N + 1)
    obtain ⟨hqp, p, rfl, hp⟩ := hq
    exact ⟨p, ⟨hp, hqp⟩, by omega⟩

/-! ### The conditional reduction

The infinitude of Sophie Germain primes is a long-standing open problem, so the main
statement below is a *conditional* one: from the existence of arbitrarily large safe
primes we deduce that the set of Sophie Germain primes is infinite. -/

/-- **Sophie Germain infinitude, conditionally.** If there are arbitrarily large safe
primes (primes of the form `2 * p + 1` with `p` prime), then there are infinitely many
Sophie Germain primes. -/
theorem SophieGermainInfinitude (hSafe : ∀ N : ℕ, ∃ q : ℕ, N < q ∧ IsSafePrime q) :
    {p : ℕ | IsSophieGermainPrime p}.Infinite := by
  rw [sophieGermain_infinite_iff_safe_infinite, infinite_iff_unbounded]
  intro N
  obtain ⟨q, hqN, hq⟩ := hSafe N
  exact ⟨q, hq, hqN⟩

end Brockian.SophieGermain

