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
-- (Lean 4 requires `import` lines to precede any module docstring `/-!`, so the header above
-- is reproduced verbatim as the module docstring immediately after the import.)

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
def IsSophieGermain (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (2 * p + 1)

/-- The set of Sophie Germain primes. -/
def sophieGermainSet : Set ℕ := {p : ℕ | IsSophieGermain p}

@[simp] theorem mem_sophieGermainSet {p : ℕ} :
    p ∈ sophieGermainSet ↔ Nat.Prime p ∧ Nat.Prime (2 * p + 1) := Iff.rfl

/-! ## Small examples (unconditional) -/

theorem isSophieGermain_two : IsSophieGermain 2 := by
  constructor <;> norm_num

theorem isSophieGermain_three : IsSophieGermain 3 := by
  constructor <;> norm_num

theorem isSophieGermain_five : IsSophieGermain 5 := by
  constructor <;> norm_num

theorem isSophieGermain_eleven : IsSophieGermain 11 := by
  constructor <;> norm_num

theorem isSophieGermain_twentythree : IsSophieGermain 23 := by
  constructor <;> norm_num

theorem isSophieGermain_eightynine : IsSophieGermain 89 := by
  constructor <;> norm_num

theorem sophieGermainSet_nonempty : sophieGermainSet.Nonempty :=
  ⟨2, isSophieGermain_two⟩

/-! ## Reformulation: infinitude is unboundedness -/

/-- The set of Sophie Germain primes is infinite iff it contains arbitrarily large elements. -/
theorem sophieGermainSet_infinite_iff_unbounded :
    sophieGermainSet.Infinite ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsSophieGermain p := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h N
    exact ⟨p, hlt, hp⟩
  · intro h N
    obtain ⟨p, hlt, hp⟩ := h N
    exact ⟨p, hp, hlt⟩

/-! ## The hypothesis: Dickson / Schinzel for two linear forms

`DicksonTwoForms` is the special case of Dickson's conjecture (equivalently, of Schinzel's
Hypothesis H for a product of two linear polynomials) asserting that an *admissible* pair of
linear forms `a * n + b`, `c * n + d` takes prime values simultaneously infinitely often.
Admissibility is the usual local condition: no prime divides the product `(a n + b)(c n + d)`
for every `n`. -/
def DicksonTwoForms : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < c →
    (∀ q : ℕ, q.Prime → ∃ n : ℕ, ¬ q ∣ (a * n + b) * (c * n + d)) →
    {n : ℕ | Nat.Prime (a * n + b) ∧ Nat.Prime (c * n + d)}.Infinite

/-- The pair of forms `n`, `2n + 1` relevant to Sophie Germain primes is admissible: no prime
divides `n * (2 * n + 1)` for every `n`. -/
theorem sophieGermain_admissible :
    ∀ q : ℕ, q.Prime → ∃ n : ℕ, ¬ q ∣ (1 * n + 0) * (2 * n + 1) := by
  intro q hq
  by_cases h3 : q = 3
  · refine ⟨2, ?_⟩
    subst h3
    decide
  · refine ⟨1, ?_⟩
    norm_num
    intro hdvd
    exact h3 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 hdvd)

/-! ## Main conditional theorem -/

/-- **Sophie Germain infinitude, conditional on Dickson's conjecture for two linear forms.**

Assuming `DicksonTwoForms` (the case of Dickson's conjecture / Schinzel's Hypothesis H for the
admissible pair of linear forms `n` and `2n + 1`), there are infinitely many Sophie Germain
primes, i.e. infinitely many primes `p` with `2 * p + 1` also prime.

The unconditional statement is a well-known open problem; this is a formally checked reduction
of it to the stated instance of Dickson's conjecture. -/
theorem SophieGermainInfinitude (H : DicksonTwoForms) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (2 * p + 1)}.Infinite := by
  have h := H 1 0 2 1 (by norm_num) (by norm_num) sophieGermain_admissible
  have hset : {n : ℕ | Nat.Prime (1 * n + 0) ∧ Nat.Prime (2 * n + 1)}
      = {p : ℕ | Nat.Prime p ∧ Nat.Prime (2 * p + 1)} := by
    ext n
    simp
  rwa [hset] at h

/-- Restatement of the conditional result in terms of `sophieGermainSet`. -/
theorem sophieGermainSet_infinite (H : DicksonTwoForms) : sophieGermainSet.Infinite :=
  SophieGermainInfinitude H

/-- Consequence: conditionally, there are arbitrarily large Sophie Germain primes. -/
theorem exists_large_sophieGermain (H : DicksonTwoForms) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ IsSophieGermain p :=
  (sophieGermainSet_infinite_iff_unbounded.1 (sophieGermainSet_infinite H)) N

end Brockian.SophieGermain

