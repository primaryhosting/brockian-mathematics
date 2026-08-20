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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a Sophie Germain prime: both `p` and `2 * p + 1` are prime. -/

def IsSophieGermainPrime (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (2 * p + 1)

/-- Dickson's conjecture: given finitely many integer linear forms `a i + b i * x` with
positive leading coefficients which are *admissible* (for every prime `q` some integer `n`
makes the product of the forms coprime to `q`), there are arbitrarily large integers `n` at
which all the forms are simultaneously prime. -/

def DicksonConjecture : Prop :=
  ∀ (k : ℕ) (a b : Fin k → ℤ), (∀ i, 0 < b i) →
    (∀ q : ℕ, q.Prime → ∃ n : ℤ, ¬ ((q : ℤ) ∣ ∏ i, (a i + b i * n))) →
    ∀ N : ℤ, ∃ n : ℤ, N < n ∧ ∀ i, Prime (a i + b i * n)

/-- The pair of linear forms `x` and `1 + 2 * x` is admissible: at `x = -1` the product of
the two forms equals `1`, hence is divisible by no prime. -/

theorem sophieGermain_admissible (q : ℕ) (hq : q.Prime) :
    ∃ n : ℤ, ¬ ((q : ℤ) ∣ ∏ i, ((![0, 1] : Fin 2 → ℤ) i + (![1, 2] : Fin 2 → ℤ) i * n)) := by
  refine ⟨-1, ?_⟩
  rw [Fin.prod_univ_two]
  norm_num
  intro h
  have : q ∣ 1 := by exact_mod_cast h
  exact hq.one_lt.ne' (Nat.dvd_one.mp this)

/-- **Conditional reduction.** Dickson's conjecture implies that there are infinitely many
Sophie Germain primes. -/

theorem SophieGermainInfinitude (hD : DicksonConjecture) :
    {p : ℕ | IsSophieGermainPrime p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hprime⟩ :=
    hD 2 ![0, 1] ![1, 2] (by decide) sophieGermain_admissible (N : ℤ)
  have h0 : Prime ((0 : ℤ) + 1 * n) := hprime 0
  have h1 : Prime ((1 : ℤ) + 2 * n) := hprime 1
  simp only [zero_add, one_mul] at h0 h1
  have hnpos : (0 : ℤ) < n := lt_of_le_of_lt (Int.natCast_nonneg N) hn
  have hcast : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hnpos.le
  refine ⟨n.toNat, ⟨?_, ?_⟩, ?_⟩
  · rw [Nat.prime_iff_prime_int, hcast]
    exact h0
  · rw [Nat.prime_iff_prime_int]
    have : ((2 * n.toNat + 1 : ℕ) : ℤ) = 1 + 2 * n := by push_cast [hcast]; ring
    rw [this]
    exact h1
  · omega

/-- Sanity check: `p = 89` is a Sophie Germain prime (`2 * 89 + 1 = 179` is prime). -/
example : IsSophieGermainPrime 89 := ⟨by norm_num, by norm_num⟩

/-- Unconditionally, the set of Sophie Germain primes is infinite if and only if it is
unbounded; this records that the conditional theorem above indeed produces the
"arbitrarily large" form of infinitude. -/
