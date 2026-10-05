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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.LandauNSquaredPlusOne

open Polynomial

/-- Landau's fourth problem: there are infinitely many primes of the form `n ^ 2 + 1`,
phrased as "for every bound `N` there is some `n > N` with `n ^ 2 + 1` prime". -/

theorem landauFourthStatement_iff_infinite :
    LandauFourthStatement ↔ {n : ℕ | Nat.Prime (n ^ 2 + 1)}.Infinite := by
  constructor
  · intro h
    rw [Set.infinite_coe_iff.symm, Set.infinite_coe_iff]
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨n, hn, hp⟩ := h N
    exact absurd (hN hp) (by omega)
  · intro h N
    obtain ⟨n, hn, hn'⟩ := h.exists_gt N
    exact ⟨n, hn', hn⟩

/-- Every prime `p` with `p ≡ 1 [MOD 4]` divides some number of the form `n ^ 2 + 1`. -/
