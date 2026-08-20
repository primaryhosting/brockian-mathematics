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

theorem isFortunate_prime_of_le_sq {n m : Nat} (h : IsFortunate n m) (hle : m ≤ n * n) :
    IsPrime m := by
  refine Classical.byContradiction fun hnp => ?_
  obtain ⟨p, hp, hpd, hpp⟩ := exists_prime_factor_sq_le m h.1 hnp
  have hpn : n < p :=
    Classical.byContradiction fun hcon => not_dvd_of_isFortunate h hp (by omega) hpd
  have : n * n < p * p := Nat.mul_self_lt_mul_self hpn
  omega

/-! ## The two degenerate indices -/

