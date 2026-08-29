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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of what is proved here

* `goldbach_beyond_of_model` is proved unconditionally (no hypothesis beyond the model datum):
  given a *model* certifying Goldbach's conjecture on a finite initial range `[4, N]`, the full
  conjecture is equivalent to its "beyond `N`" form.
* A model for `N = 400` (`model400`) is constructed and proved by kernel computation, so
  `goldbach_iff_beyond_400` is likewise unconditional.
* Goldbach's conjecture itself (`Goldbach`) is *not* proved here; it is an open problem, and
  nothing in this file asserts it.  Everything stated is either unconditional or explicitly
  conditional on `Goldbach` (see `ternary_of_goldbach`).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.GoldbachSchema

/-- `IsGoldbach n` : the natural number `n` is a sum of two primes. -/
def IsGoldbach (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Goldbach's conjecture: every even number `n ≥ 4` is a sum of two primes. -/
def Goldbach : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → IsGoldbach n

/-- The "beyond `N`" form of Goldbach's conjecture: every even number `n ≥ 4` with `N < n`
is a sum of two primes. -/
def GoldbachBeyond (N : ℕ) : Prop :=
  ∀ n : ℕ, 4 ≤ n → N < n → Even n → IsGoldbach n

/-- A *Goldbach model up to `N`* is a certificate that Goldbach's conjecture holds throughout
the finite initial range `[4, N]`.  Such certificates are decidable finite objects: one is
constructed explicitly for `N = 400` below (`model400`). -/
structure GoldbachModel (N : ℕ) : Prop where
  /-- Every even `n` with `4 ≤ n ≤ N` is a sum of two primes. -/
  certificate : ∀ n : ℕ, 4 ≤ n → n ≤ N → Even n → IsGoldbach n

/-- **Main theorem.**  Relative to a Goldbach model up to `N`, the full Goldbach conjecture is
*equivalent* to its "beyond `N`" form: the finite initial segment of the conjecture is
discharged by the model, so nothing but the tail remains.

This statement is unconditional: it carries no unproven hypothesis, only the finite (and
explicitly constructible) model datum. -/
theorem goldbach_beyond_of_model {N : ℕ} (M : GoldbachModel N) :
    Goldbach ↔ GoldbachBeyond N := by
  constructor
  · intro h n hn _ hev
    exact h n hn hev
  · intro h n hn hev
    rcases Nat.lt_or_ge N n with hlt | hle
    · exact h n hn hlt hev
    · exact M.certificate n hn hle hev

/-- The finite verification underlying the model: every even `n` with `4 ≤ n ≤ 400` is a sum of
two primes.  This is checked by kernel computation. -/
theorem goldbach_upTo_400 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 400 → Even n → IsGoldbach n := by
  have key : ∀ n ∈ Finset.range 401, 4 ≤ n → n % 2 = 0 →
      ∃ p ∈ Finset.range (n + 1), Nat.Prime p ∧ Nat.Prime (n - p) := by decide
  intro n hn hle hev
  have hn2 : n % 2 = 0 := Nat.even_iff.mp hev
  obtain ⟨p, hp, hpp, hqp⟩ := key n (Finset.mem_range.mpr (by omega)) hn hn2
  have hple : p ≤ n := by
    have := Finset.mem_range.mp hp
    omega
  exact ⟨p, n - p, hpp, hqp, by omega⟩

/-- An explicit Goldbach model up to `400`. -/
theorem model400 : GoldbachModel 400 := ⟨goldbach_upTo_400⟩

/-- Goldbach's conjecture is equivalent to its "beyond `400`" form. -/
theorem goldbach_iff_beyond_400 : Goldbach ↔ GoldbachBeyond 400 :=
  goldbach_beyond_of_model model400

/-- The ternary form of Goldbach's conjecture follows from the binary one: if every even
number `≥ 4` is a sum of two primes, then every odd number `≥ 9` is a sum of three primes. -/
theorem ternary_of_goldbach (h : Goldbach) :
    ∀ n : ℕ, 9 ≤ n → Odd n → ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n := by
  intro n hn hodd
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨p, q, hp, hq, hpq⟩ := h (n - 3) (by omega) ⟨k - 1, by omega⟩
  exact ⟨p, q, 3, hp, hq, Nat.prime_three, by omega⟩

/-- An unconditional Goldbach-flavoured result: every natural number `n ≥ 2` is the sum of a
(finite, nonempty) list of primes. -/
theorem exists_list_primes_sum : ∀ n : ℕ, 2 ≤ n →
    ∃ l : List ℕ, l ≠ [] ∧ (∀ p ∈ l, Nat.Prime p) ∧ l.sum = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · interval_cases n
      · exact ⟨[2], by simp, by simp [Nat.prime_two], by simp⟩
      · exact ⟨[3], by simp, by simp [Nat.prime_three], by simp⟩
    · obtain ⟨l, hne, hp, hs⟩ := ih (n - 2) (by omega) (by omega)
      refine ⟨2 :: l, by simp, ?_, ?_⟩
      · intro p hp'
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact Nat.prime_two
        · exact hp p hp'
      · simp only [List.sum_cons, hs]; omega

end Brockian.GoldbachSchema

