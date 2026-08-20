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
import Brockian.LegendreConjecture

/-!
# Legendre Conjecture — Mathlib companion

This module connects the self-contained statements of `Brockian.LegendreConjecture`
(which, by design, imports nothing so that the required header comment can sit at the
very top of that file) with Mathlib's `Nat.Prime`, and records some unconditional
partial results towards Legendre's conjecture.
-/

namespace Brockian.LegendreConjecture

/-- The self-contained primality predicate used in `Brockian.LegendreConjecture`
agrees with Mathlib's `Nat.Prime`. -/

theorem isPrime_iff_natPrime (p : Nat) : IsPrime p ↔ Nat.Prime p := by
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hmp hdvd => h m hmp hm ?_⟩
    exact Nat.mod_eq_zero_of_dvd hdvd
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hmp hm hmod => h m hm hmp ?_⟩
    exact Nat.dvd_of_mod_eq_zero hmod

/-- Legendre's statement, phrased with Mathlib's `Nat.Prime`, is equivalent to the
statement `LegendreStatement` used in the main file. -/
