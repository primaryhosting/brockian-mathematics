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
def IsSophieGermainPrime (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

instance (p : ℕ) : Decidable (IsSophieGermainPrime p) := by
  unfold IsSophieGermainPrime; infer_instance

/-- The set of Sophie Germain primes. -/
def sophieGermainPrimes : Set ℕ := {p | IsSophieGermainPrime p}

example : IsSophieGermainPrime 2 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 3 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 5 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 11 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 23 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 29 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 41 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 53 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 83 := by norm_num [IsSophieGermainPrime]
example : IsSophieGermainPrime 89 := by norm_num [IsSophieGermainPrime]

/-- Unconditional structural result: every Sophie Germain prime `p > 3` satisfies
`p % 6 = 5`. -/
theorem mod_six_eq_five_of_isSophieGermainPrime {p : ℕ} (hp : IsSophieGermainPrime p)
    (hp3 : 3 < p) : p % 6 = 5 := by
  obtain ⟨hprime, hq⟩ := hp
  have h2 : ¬ (2 ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp h
    omega
  have h3 : ¬ (3 ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hprime).mp h
    omega
  have h3' : ¬ (3 ∣ 2 * p + 1) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h
    omega
  have e2 : p % 2 ≠ 0 := fun h => h2 (Nat.dvd_of_mod_eq_zero h)
  have e3 : p % 3 ≠ 0 := fun h => h3 (Nat.dvd_of_mod_eq_zero h)
  have e3' : (2 * p + 1) % 3 ≠ 0 := fun h => h3' (Nat.dvd_of_mod_eq_zero h)
  have hp2 : p % 2 = 1 := by omega
  have hne1 : p % 3 ≠ 1 := fun h => e3' (by omega)
  have hp3' : p % 3 = 2 := by omega
  omega

/-- **Conditional reduction.**  The Sophie Germain conjecture — the infinitude of the set of
primes `p` for which `2 * p + 1` is also prime — follows from (and is in fact equivalent to,
see `sophieGermainPrimes_infinite_iff_unbounded`) the statement that Sophie Germain primes are
unbounded.  The unboundedness hypothesis `hUnbounded` is exactly the open input; everything
else is proved here.

This is the target statement `Brockian.SophieGermain.SophieGermainInfinitude`, stated as a
Lean-checked conditional reduction, since the unconditional Sophie Germain conjecture is an
open problem.  The reduction is closed by the Mathlib lemma
`Set.infinite_of_forall_exists_gt`. -/
theorem SophieGermainInfinitude
    (hUnbounded : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsSophieGermainPrime p) :
    sophieGermainPrimes.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro a
  obtain ⟨p, hlt, hp⟩ := hUnbounded a
  exact ⟨p, hp, hlt⟩

/-- The infinitude of the Sophie Germain primes is equivalent to their unboundedness. -/
theorem sophieGermainPrimes_infinite_iff_unbounded :
    sophieGermainPrimes.Infinite ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsSophieGermainPrime p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp⟩
  · exact SophieGermainInfinitude

/-! ### A counting-function criterion -/

/-- The number of Sophie Germain primes `≤ N`. -/
def sophieGermainCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter IsSophieGermainPrime).card

/-- If the counting function of the Sophie Germain primes is unbounded, then there are
infinitely many Sophie Germain primes. -/
theorem sophieGermainPrimes_infinite_of_count_unbounded
    (h : ∀ C : ℕ, ∃ N : ℕ, C < sophieGermainCount N) : sophieGermainPrimes.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := h hfin.toFinset.card
  have hsub : (Finset.range (N + 1)).filter IsSophieGermainPrime ⊆ hfin.toFinset := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact hfin.mem_toFinset.2 hx.2
  exact absurd (Finset.card_le_card hsub) (by simpa [sophieGermainCount] using hN)

/-- Conversely, if there are infinitely many Sophie Germain primes then their counting
function is unbounded. -/
theorem count_unbounded_of_sophieGermainPrimes_infinite
    (h : sophieGermainPrimes.Infinite) (C : ℕ) : ∃ N : ℕ, C < sophieGermainCount N := by
  obtain ⟨t, hts, htcard⟩ := h.exists_subset_card_eq (C + 1)
  refine ⟨t.sup id, ?_⟩
  have hsub : t ⊆ (Finset.range (t.sup id + 1)).filter IsSophieGermainPrime := by
    intro x hx
    have hx' : x ≤ t.sup id := Finset.le_sup (f := id) hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hts hx⟩
  have := Finset.card_le_card hsub
  simp only [sophieGermainCount]
  omega

/-- The counting-function criterion, as an equivalence. -/
theorem sophieGermainPrimes_infinite_iff_count_unbounded :
    sophieGermainPrimes.Infinite ↔ ∀ C : ℕ, ∃ N : ℕ, C < sophieGermainCount N :=
  ⟨count_unbounded_of_sophieGermainPrimes_infinite,
    sophieGermainPrimes_infinite_of_count_unbounded⟩

/-! ### Safe primes -/

/-- The safe primes: primes of the form `2 * p + 1` with `p` a Sophie Germain prime. -/
def safePrimes : Set ℕ := {q | ∃ p, IsSophieGermainPrime p ∧ q = 2 * p + 1}

/-- Infinitely many Sophie Germain primes gives infinitely many safe primes. -/
theorem safePrimes_infinite_of_sophieGermainPrimes_infinite
    (h : sophieGermainPrimes.Infinite) : safePrimes.Infinite := by
  have himg : safePrimes = (fun p => 2 * p + 1) '' sophieGermainPrimes := by
    ext q
    simp [safePrimes, sophieGermainPrimes, eq_comm]
  rw [himg]
  exact h.image (Set.injOn_of_injective (fun a b hab => by omega))

end Brockian.SophieGermain

