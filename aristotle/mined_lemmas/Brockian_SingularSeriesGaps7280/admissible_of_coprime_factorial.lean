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
# Admissible tuples and positivity of the singular series

An `H : Finset ℕ` (thought of as a set of *gaps* / offsets of a prime constellation
`n + h`, `h ∈ H`) is **admissible** when, for every prime `p`, the reductions of `H`
modulo `p` do not cover all residue classes.  This is exactly the condition under which
the local factors of the Hardy–Littlewood singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p) (1 - 1/p)^(-|H|)` are all positive.

This file develops the basic theory and a general criterion producing admissible sets:
a set of size at most `m`, all of whose elements are coprime to `m !`, is admissible.
-/

open scoped BigOperators Nat

namespace Brockian

/-- The number of residue classes mod `p` occupied by `H`, i.e. `ν_H(p)`. -/

theorem admissible_of_coprime_factorial {H : Finset ℕ} {m : ℕ} (hcard : H.card ≤ m)
    (hcop : ∀ n ∈ H, Nat.Coprime n (m !)) : Admissible H := by
  refine admissible_iff_residueCount_lt.2 fun p hp => ?_
  by_cases hpm : p ≤ m
  · refine residueCount_lt_of_miss hp.pos hp.pos ?_
    intro h hh hcon
    have hdvd : p ∣ h := Nat.dvd_of_mod_eq_zero hcon
    have hgcd : p ∣ Nat.gcd h (m !) := Nat.dvd_gcd hdvd (Nat.dvd_factorial hp.pos hpm)
    rw [hcop h hh] at hgcd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hgcd)
  · push_neg at hpm
    exact lt_of_le_of_lt (residueCount_le_card H p) (lt_of_le_of_lt hcard hpm)

/-- **Admissible gap ranges.**  Inside any window `[1, N]`, the integers with no prime
factor `≤ m` form an admissible set of gaps as soon as there are at most `m` of them. -/
