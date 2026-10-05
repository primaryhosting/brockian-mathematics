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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Finset

/-- `IsFortunate n m` says that `m` is the *fortunate number* attached to the primorial `n#`:
it is the least integer `m > 1` such that `n# + m` is prime. -/

theorem fortuneConjecture_of_lt_next_prime_sq
    (hgap : ∀ n m r : ℕ, IsFortunate n m → (∀ q : ℕ, Nat.Prime q → n < q → r ≤ q) → m < r ^ 2) :
    ∀ n m : ℕ, IsFortunate n m → Nat.Prime m := by
  intro n m hm
  obtain ⟨r, -, hrmin⟩ : ∃ r : ℕ, Nat.Prime r ∧ ∀ q : ℕ, Nat.Prime q → n < q → r ≤ q := by
    have hne : {q : ℕ | Nat.Prime q ∧ n < q}.Nonempty := by
      obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (n + 1)
      exact ⟨p, hp, by omega⟩
    obtain ⟨hr1, -⟩ := Nat.sInf_mem hne
    exact ⟨_, hr1, fun q hq hqn => Nat.sInf_le ⟨hq, hqn⟩⟩
  exact prime_of_prime_primorial_add_of_lt_sq hm.1.1 hm.1.2 hrmin (hgap n m r hm hrmin)

/-- Unconditional instance: the fortunate number attached to `7# = 210` is `13`, which is prime. -/
