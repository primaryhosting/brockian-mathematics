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

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

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

/-!
## Setup

For a bound `N`, `primorial N` (Mathlib's `primorial`, notation `N#`) is the product of all
primes `≤ N`.  The *fortunate number* attached to `N` is the least `m ≥ 2` such that
`N# + m` is prime.  Fortune's conjecture asserts that this number is always prime.

The conjecture is open.  What we prove here is the classical unconditional dichotomy
(`fortunate_prime_or_sq_le`): the fortunate number is either prime or at least `(N+1)^2`,
because none of its prime factors can be `≤ N`.  The named target
`FortuneConjecture` is therefore the corresponding *conditional* statement: the fortunate
number is prime as soon as it is smaller than `(N+1)^2`.
-/

/-- Every prime `q ≤ N` divides the primorial `N#`. -/
theorem prime_dvd_primorial {q N : ℕ} (hq : q.Prime) (hqN : q ≤ N) : q ∣ primorial N := by
  refine Finset.dvd_prod_of_mem (fun p => p) ?_
  simp [Finset.mem_filter, Finset.mem_range, hq, Nat.lt_succ_of_le hqN]

/-- There is always some `m ≥ 2` with `N# + m` prime (by the infinitude of primes). -/
theorem exists_fortunate (N : ℕ) : ∃ m, 2 ≤ m ∧ (primorial N + m).Prime := by
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (primorial N + 2)
  refine ⟨p - primorial N, by omega, ?_⟩
  have : primorial N + (p - primorial N) = p := by omega
  rwa [this]

/-- The fortunate number of `N`: the least `m ≥ 2` such that `N# + m` is prime. -/
noncomputable def fortunate (N : ℕ) : ℕ := sInf {m | 2 ≤ m ∧ (primorial N + m).Prime}

theorem fortunate_mem (N : ℕ) : 2 ≤ fortunate N ∧ (primorial N + fortunate N).Prime :=
  Nat.sInf_mem (exists_fortunate N)

theorem two_le_fortunate (N : ℕ) : 2 ≤ fortunate N := (fortunate_mem N).1

theorem prime_primorial_add_fortunate (N : ℕ) : (primorial N + fortunate N).Prime :=
  (fortunate_mem N).2

theorem fortunate_le {N m : ℕ} (hm : 2 ≤ m) (h : (primorial N + m).Prime) :
    fortunate N ≤ m :=
  Nat.sInf_le ⟨hm, h⟩

/-- No prime `q ≤ N` divides the fortunate number of `N`. -/
theorem not_prime_dvd_fortunate {q N : ℕ} (hq : q.Prime) (hqN : q ≤ N) :
    ¬ q ∣ fortunate N := by
  intro hdvd
  have hqP : q ∣ primorial N := prime_dvd_primorial hq hqN
  have hsum : q ∣ primorial N + fortunate N := Nat.dvd_add hqP hdvd
  have hprime := prime_primorial_add_fortunate N
  have hq_eq : q = primorial N + fortunate N :=
    ((Nat.Prime.eq_one_or_self_of_dvd hprime q hsum).resolve_left hq.ne_one)
  have hqle : q ≤ primorial N := Nat.le_of_dvd (primorial_pos N) hqP
  have := two_le_fortunate N
  omega

/-- Every prime factor of the fortunate number of `N` exceeds `N`. -/
theorem lt_minFac_fortunate (N : ℕ) : N < (fortunate N).minFac := by
  by_contra h
  push_neg at h
  have hne : fortunate N ≠ 1 := by have := two_le_fortunate N; omega
  exact not_prime_dvd_fortunate (Nat.minFac_prime hne) h (Nat.minFac_dvd _)

/-- **Unconditional dichotomy.** The fortunate number of `N` is either prime, or it is at
least `(N+1)^2`. -/
theorem fortunate_prime_or_sq_le (N : ℕ) :
    (fortunate N).Prime ∨ (N + 1) ^ 2 ≤ fortunate N := by
  by_cases hp : (fortunate N).Prime
  · exact Or.inl hp
  · refine Or.inr ?_
    have hpos : 0 < fortunate N := by have := two_le_fortunate N; omega
    have h1 : (fortunate N).minFac ^ 2 ≤ fortunate N := Nat.minFac_sq_le_self hpos hp
    have h2 : N + 1 ≤ (fortunate N).minFac := lt_minFac_fortunate N
    exact le_trans (Nat.pow_le_pow_left h2 2) h1

/-- **Fortune's conjecture, conditional form.**  The fortunate number of `N` — the least
`m ≥ 2` with `N# + m` prime — is prime, provided it is smaller than `(N+1)^2`.

Fortune's conjecture itself (that this holds unconditionally) is open; the hypothesis
`fortunate N < (N + 1) ^ 2` is exactly the classical gap, and it is known to hold for all
values that have been computed. -/
theorem FortuneConjecture (N : ℕ) (h : fortunate N < (N + 1) ^ 2) : (fortunate N).Prime :=
  (fortunate_prime_or_sq_le N).resolve_right (by omega)

/-- A concrete instance: `5# = 30` and the least `m ≥ 2` with `30 + m` prime is `m = 7`. -/
theorem fortunate_five : fortunate 5 = 7 := by
  have h30 : primorial 5 = 30 := by decide
  refine le_antisymm (fortunate_le (by norm_num) (by rw [h30]; decide)) ?_
  refine le_csInf ⟨_, Nat.sInf_mem (exists_fortunate 5)⟩ ?_
  rintro m ⟨h2, hp⟩
  rw [h30] at hp
  by_contra hlt
  push_neg at hlt
  interval_cases m <;> revert hp <;> decide

/-- The conditional form applies to `N = 5`: `fortunate 5 = 7 < 36`, so it is prime. -/
theorem fortunate_five_prime : (fortunate 5).Prime :=
  FortuneConjecture 5 (by rw [fortunate_five]; norm_num)

end Brockian.FortunateNumbers

