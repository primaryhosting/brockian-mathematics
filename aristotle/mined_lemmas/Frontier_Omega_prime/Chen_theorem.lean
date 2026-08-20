/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `Omega n` is the number of prime factors of `n`, counted with multiplicity
(the classical arithmetic function `Ω`). -/

theorem Chen_theorem :
    ChenStatement ↔ {n : ℕ | Even n ∧ ¬ IsChenSum n}.Finite := by
  constructor
  · rintro ⟨N, hN⟩
    refine Set.Finite.subset (Set.finite_Iio N) ?_
    rintro n ⟨hev, hns⟩
    by_contra hlt
    exact hns (hN n (le_of_not_gt hlt) hev)
  · intro hfin
    obtain ⟨M, hM⟩ := hfin.bddAbove
    refine ⟨M + 1, fun n hn hev => ?_⟩
    by_contra hns
    have : n ≤ M := hM ⟨hev, hns⟩
    omega

end Frontier

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

