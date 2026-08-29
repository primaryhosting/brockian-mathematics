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

-- (The header above is a plain block comment rather than a `/-!` module docstring only because
-- Lean 4 requires `import` commands to precede every command in a file, including docstrings.)

import Mathlib

/-!
# Betrothed Infinitude

## Betrothed (quasi-amicable) numbers

Two distinct positive integers `m ≠ n` are *betrothed* (or *quasi-amicable*) when each is the
sum of the proper divisors of the other, where "proper divisor" here excludes both `1` and the
number itself.  Equivalently

```
σ m = σ n = m + n + 1,
```

with `σ = ArithmeticFunction.sigma 1` the usual sum-of-divisors function.

Whether there are infinitely many betrothed pairs is an open problem, so the headline theorem
`BetrothedInfinitude` below is stated as a *conditional reduction*: from the (open) hypothesis
that betrothed numbers are unbounded we deduce that the set of betrothed pairs is infinite, and
`betrothed_infinite_iff_unbounded` shows that the two formulations are in fact equivalent.
Unconditionally we verify a list of explicit betrothed pairs.
-/

namespace Brockian.BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/
abbrev sigmaOne (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- `m` and `n` form a *betrothed pair*: they are distinct positive integers each of which is
the sum of the proper divisors of the other, where proper divisors exclude both `1` and the
number itself. -/
def IsBetrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

instance (m n : ℕ) : Decidable (IsBetrothed m n) := inferInstanceAs (Decidable (_ ∧ _))

/-- Being betrothed is a symmetric relation. -/
theorem IsBetrothed.symm {m n : ℕ} (h : IsBetrothed m n) : IsBetrothed n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  refine ⟨hn, hm, hne.symm, ?_, ?_⟩ <;> omega

/-- The partner of a betrothed number is determined by it. -/
theorem IsBetrothed.partner_unique {m n n' : ℕ} (h : IsBetrothed m n) (h' : IsBetrothed m n') :
    n = n' := by
  obtain ⟨-, -, -, h1, -⟩ := h
  obtain ⟨-, -, -, h1', -⟩ := h'
  omega

/-- The classical phrasing: for a betrothed pair, the sum of the proper divisors of `m`
(the divisors `< m`, so including `1`) is `n + 1`. -/
theorem IsBetrothed.sum_properDivisors {m n : ℕ} (h : IsBetrothed m n) :
    ∑ d ∈ m.properDivisors, d = n + 1 := by
  obtain ⟨-, -, -, h1, -⟩ := h
  have hs : sigmaOne m = ∑ d ∈ m.divisors, d := by
    simp [sigmaOne, ArithmeticFunction.sigma_apply]
  have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := m)
  omega

/-- Conversely, the "sum of proper divisors" phrasing implies betrothal. -/
theorem isBetrothed_of_sum_properDivisors {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (h1 : ∑ d ∈ m.properDivisors, d = n + 1) (h2 : ∑ d ∈ n.properDivisors, d = m + 1) :
    IsBetrothed m n := by
  have hsm : sigmaOne m = ∑ d ∈ m.divisors, d := by
    simp [sigmaOne, ArithmeticFunction.sigma_apply]
  have hsn : sigmaOne n = ∑ d ∈ n.divisors, d := by
    simp [sigmaOne, ArithmeticFunction.sigma_apply]
  have em := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := m)
  have en := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := n)
  exact ⟨hm, hn, hmn, by omega, by omega⟩

/-! ### Explicit betrothed pairs -/

set_option maxRecDepth 8000000

theorem betrothed_48_75 : IsBetrothed 48 75 := by decide

theorem betrothed_140_195 : IsBetrothed 140 195 := by decide

theorem betrothed_1050_1925 : IsBetrothed 1050 1925 := by decide

theorem betrothed_1575_1648 : IsBetrothed 1575 1648 := by decide

theorem betrothed_2024_2295 : IsBetrothed 2024 2295 := by decide

theorem betrothed_5775_6128 : IsBetrothed 5775 6128 := by decide

theorem betrothed_8892_16587 : IsBetrothed 8892 16587 := by decide

/-! ### The reduction -/

/-- The set of all betrothed pairs. -/
def betrothedPairs : Set (ℕ × ℕ) := {p : ℕ × ℕ | IsBetrothed p.1 p.2}

/-- **Betrothed Infinitude (conditional reduction).**

Whether there are infinitely many betrothed pairs is an open problem; what is proved here is
the reduction of that statement to the unboundedness of betrothed numbers: if for every bound
`N` there is a betrothed pair `(m, n)` with `m > N`, then the set of betrothed pairs is
infinite. -/
theorem BetrothedInfinitude
    (unbounded : ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothed m n) :
    betrothedPairs.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := (hfin.image Prod.fst).bddAbove
  obtain ⟨m, n, hm, hmn⟩ := unbounded N
  have hmem : m ∈ Prod.fst '' betrothedPairs := ⟨(m, n), hmn, rfl⟩
  exact absurd (hN hmem) (by omega)

/-- The converse direction: an infinite set of betrothed pairs forces betrothed numbers to be
unbounded.  Together with `BetrothedInfinitude` this makes the reduction an equivalence. -/
theorem betrothed_infinite_iff_unbounded :
    betrothedPairs.Infinite ↔ ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothed m n := by
  refine ⟨fun hinf N => ?_, BetrothedInfinitude⟩
  by_contra hcon
  push_neg at hcon
  have hsub : betrothedPairs ⊆ Set.Iic N ×ˢ Set.Iic N := by
    rintro ⟨m, n⟩ hp
    have hb : IsBetrothed m n := hp
    have hm : m ≤ N := by
      by_contra hm
      exact absurd hb (hcon m n (by omega))
    have hn : n ≤ N := by
      by_contra hn
      exact absurd hb.symm (hcon n m (by omega))
    exact ⟨hm, hn⟩
  exact hinf (((Set.finite_Iic N).prod (Set.finite_Iic N)).subset hsub)

/-- Unconditionally, there is at least one betrothed pair. -/
theorem betrothedPairs_nonempty : betrothedPairs.Nonempty :=
  ⟨(48, 75), betrothed_48_75⟩

end Brockian.BetrothedNumbers

