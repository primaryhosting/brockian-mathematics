import Brockian.GoldbachSchema

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

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian
namespace GoldbachSchema

/-- The Goldbach property: `n` is a sum of two primes. -/
def IsGoldbach (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- The strong Goldbach property: `n` is a sum of two *distinct odd* primes. -/
def IsStrongGoldbach (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧ p ≠ q ∧ n = p + q

theorem IsStrongGoldbach.isGoldbach {n : ℕ} (h : IsStrongGoldbach n) : IsGoldbach n := by
  obtain ⟨p, q, hp, hq, _, _, _, hsum⟩ := h
  exact ⟨p, q, hp, hq, hsum⟩

/-- A *model of the Goldbach schema beyond `N`*: a concrete even number `n > N`
together with a certified representation of `n` as a sum of two distinct odd primes. -/
structure Model (N : ℕ) where
  /-- The even number witnessing the schema. -/
  n : ℕ
  /-- The first prime summand. -/
  p : ℕ
  /-- The second prime summand. -/
  q : ℕ
  /-- The witness lies beyond the scale `N`. -/
  lt : N < n
  /-- The witness is even. -/
  even : Even n
  /-- `p` is prime. -/
  hp : Nat.Prime p
  /-- `q` is prime. -/
  hq : Nat.Prime q
  /-- `p` is odd. -/
  hp_odd : Odd p
  /-- `q` is odd. -/
  hq_odd : Odd q
  /-- The two prime summands are distinct. -/
  hne : p ≠ q
  /-- `n` is the sum of the two primes. -/
  hsum : n = p + q

/-- **Discharge of the named hypothesis.**  The Goldbach schema admits a model beyond
every scale `N`: given `N`, pick a prime `p ≥ max (N + 1) 5` and take `n = p + 3`. -/
theorem model_exists (N : ℕ) : Nonempty (Model N) := by
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max (N + 1) 5)
  have h5 : 5 ≤ p := le_trans (le_max_right _ _) hple
  have hN : N + 1 ≤ p := le_trans (le_max_left _ _) hple
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  refine ⟨{ n := p + 3, p := p, q := 3, lt := by omega, even := hpodd.add_odd (by decide),
            hp := hp, hq := by norm_num, hp_odd := hpodd, hq_odd := by decide,
            hne := by omega, hsum := rfl }⟩

/-- **Goldbach beyond every scale.**

Originally stated relative to the named hypothesis `hmodel : ∀ N, Nonempty (Model N)`,
this is now unconditional: that hypothesis is discharged by `model_exists`.

For every bound `N` there is an even number `n > N` which is the sum of two distinct
odd primes.  (The full Goldbach conjecture — *every* even `n ≥ 4` is such a sum — remains
open; this is the unbounded-witness form of the schema.) -/
theorem goldbach_beyond_of_model :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Even n ∧ IsStrongGoldbach n := by
  intro N
  obtain ⟨M⟩ := model_exists N
  exact ⟨M.n, M.lt, M.even, M.p, M.q, M.hp, M.hq, M.hp_odd, M.hq_odd, M.hne, M.hsum⟩

/-- The set of even numbers satisfying the strong Goldbach property is infinite. -/
theorem goldbach_beyond_infinite :
    {n : ℕ | Even n ∧ IsStrongGoldbach n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro a
  obtain ⟨n, hlt, heven, hgold⟩ := goldbach_beyond_of_model a
  exact ⟨n, ⟨heven, hgold⟩, hlt⟩

/-- Base of the schema: the Goldbach property is verified for every even `n` with
`4 ≤ n ≤ 100`. -/
theorem goldbach_initial_segment (n : ℕ) (h4 : 4 ≤ n) (h100 : n ≤ 100) (hn : Even n) :
    IsGoldbach n := by
  have key : ∀ m ∈ Finset.Icc 4 100, Even m →
      ∃ p ∈ Finset.range (m + 1), ∃ q ∈ Finset.range (m + 1),
        Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by decide
  obtain ⟨p, _, q, _, hp, hq, hsum⟩ := key n (Finset.mem_Icc.mpr ⟨h4, h100⟩) hn
  exact ⟨p, q, hp, hq, hsum⟩

end GoldbachSchema
end Brockian

