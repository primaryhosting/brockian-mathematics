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

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, which Lean parses as a
command, so no `import` line may follow it.  The whole development below is therefore
self-contained and uses only the Lean 4 core library (no Mathlib).
-/

namespace Brockian.FortunateNumbers

/-! ## Primality and the primorial -/

/-- `IsPrime p` : `p` is a prime natural number. -/

theorem exists_prime_gt (N : Nat) : ∃ p, IsPrime p ∧ N < p := by
  have h2 : 2 ≤ fact N + 1 := by have := fact_pos N; omega
  obtain ⟨p, hp, hpd⟩ := exists_prime_dvd (fact N + 1) h2
  refine ⟨p, hp, Classical.byContradiction fun hle => ?_⟩
  have hpN : p ∣ fact N := dvd_fact (by have := hp.two_le; omega) (by omega)
  have hd1 : p ∣ 1 := by
    have hsub := Nat.dvd_sub hpd hpN
    have he : fact N + 1 - fact N = 1 := by omega
    rwa [he] at hsub
  have := Nat.le_of_dvd Nat.zero_lt_one hd1
  have := hp.two_le
  omega

/-! ## Fortunate numbers -/

/-- `IsFortunate n m` says that `m` is the `n`-th **fortunate number**: the least `m > 1`
such that `primorial n + m` is prime. -/
