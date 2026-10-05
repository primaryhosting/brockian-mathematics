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

/-- The sum-of-divisors function `σ₁`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `sigma1` agrees with Mathlib's arithmetic function `σ₁`. -/
theorem sigma1_eq_sigma_one (n : ℕ) : sigma1 n = ArithmeticFunction.sigma 1 n := by
  simp [sigma1, ArithmeticFunction.sigma_apply]

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: each is the sum of the
*nontrivial* proper divisors of the other, i.e. `σ(m) = σ(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ m < n ∧ sigma1 m = m + n + 1 ∧ sigma1 n = m + n + 1

instance (m n : ℕ) : Decidable (IsBetrothedPair m n) := by
  unfold IsBetrothedPair; infer_instance

/-- The candidate partner of `m`, determined by `m` alone. -/
def partner (m : ℕ) : ℕ := sigma1 m - m - 1

/-- `m` is the smaller member of a betrothed pair. This is a decidable predicate of the
single variable `m`. -/
def IsBetrothedSmaller (m : ℕ) : Prop := IsBetrothedPair m (partner m)

instance (m : ℕ) : Decidable (IsBetrothedSmaller m) := by
  unfold IsBetrothedSmaller; infer_instance

/-- In a betrothed pair the larger member is determined by the smaller one. -/
theorem partner_eq_of_isBetrothedPair {m n : ℕ} (h : IsBetrothedPair m n) : n = partner m := by
  obtain ⟨-, -, h1, -⟩ := h
  simp only [partner, h1]
  omega

/-- Betrothed pairs are exactly the pairs `(m, partner m)` with `m` betrothed-smaller:
the two–variable search reduces to a decidable one–variable search. -/
theorem isBetrothedPair_iff (m n : ℕ) :
    IsBetrothedPair m n ↔ IsBetrothedSmaller m ∧ n = partner m := by
  constructor
  · intro h
    have hn := partner_eq_of_isBetrothedPair h
    refine ⟨?_, hn⟩
    rw [IsBetrothedSmaller, ← hn]
    exact h
  · rintro ⟨h, rfl⟩
    exact h

/-- The set of betrothed pairs. -/
def betrothedPairs : Set (ℕ × ℕ) := {p : ℕ × ℕ | IsBetrothedPair p.1 p.2}

/-- The set of smaller members of betrothed pairs. -/
def betrothedSmallerSet : Set ℕ := {m : ℕ | IsBetrothedSmaller m}

set_option maxRecDepth 100000 in
/-- The smallest betrothed pair. -/
theorem isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by decide

set_option maxRecDepth 100000 in
theorem isBetrothedPair_140_195 : IsBetrothedPair 140 195 := by decide

set_option maxRecDepth 100000 in
theorem isBetrothedPair_1050_1925 : IsBetrothedPair 1050 1925 := by decide

set_option maxRecDepth 100000 in
theorem isBetrothedPair_1575_1648 : IsBetrothedPair 1575 1648 := by decide

set_option maxRecDepth 100000 in
theorem isBetrothedPair_2024_2295 : IsBetrothedPair 2024 2295 := by decide

/-- If the smaller members of betrothed pairs are unbounded, there are infinitely many of them. -/
theorem betrothedSmallerSet_infinite
    (h : ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothedPair m n) :
    betrothedSmallerSet.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro a
  obtain ⟨m, n, ham, hmn⟩ := h a
  exact ⟨m, ((isBetrothedPair_iff m n).1 hmn).1, ham⟩

/-- **Betrothed Infinitude (conditional reduction).**

If for every bound `N` there exists a betrothed (quasi-amicable) pair `(m, n)` with `m > N`,
then there are infinitely many betrothed pairs. -/
theorem BetrothedInfinitude
    (h : ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothedPair m n) :
    betrothedPairs.Infinite := by
  intro hfin
  refine (betrothedSmallerSet_infinite h) ?_
  refine (hfin.image Prod.fst).subset ?_
  intro m hm
  exact ⟨(m, partner m), hm, rfl⟩

/-- Conversely, infinitely many betrothed pairs means unboundedly large ones. -/
theorem unbounded_of_betrothedPairs_infinite (h : betrothedPairs.Infinite) :
    ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothedPair m n := by
  intro N
  by_contra hc
  push_neg at hc
  have hsub : betrothedPairs ⊆ (fun m => (m, partner m)) '' Set.Iic N := by
    rintro ⟨m, n⟩ hp
    have hn : n = partner m := partner_eq_of_isBetrothedPair hp
    have hle : m ≤ N := by
      by_contra hlt
      exact hc m n (lt_of_not_ge hlt) hp
    exact ⟨m, hle, by simp [hn]⟩
  exact h (((Set.finite_Iic N).image _).subset hsub)

/-- The conjecture is equivalent to the unboundedness statement. -/
theorem betrothedPairs_infinite_iff :
    betrothedPairs.Infinite ↔ ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothedPair m n :=
  ⟨unbounded_of_betrothedPairs_infinite, BetrothedInfinitude⟩

end Brockian.BetrothedNumbers

