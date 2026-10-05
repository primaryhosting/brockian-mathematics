import Mathlib

/-!
# Conjecture Statement
Category: Frontier — Prime Numbers
Target: Twin.conjecture_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Twin

/-- The twin prime conjecture, as a `Prop`: for every bound `N` there is a prime `p > N`
such that `p + 2` is also prime.  This is only *stated* here; it is not proved. -/

theorem twinPrimeConj_iff_infinite :
    TwinPrimeConj ↔ {p : Nat | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  constructor
  · intro h
    rw [Set.infinite_iff_exists_gt]
    intro a
    obtain ⟨p, hp, hp1, hp2⟩ := h a
    exact ⟨p, ⟨hp1, hp2⟩, hp⟩
  · intro h N
    obtain ⟨p, hp, hlt⟩ := (Set.infinite_iff_exists_gt.mp h) N
    exact ⟨p, hlt, hp.1, hp.2⟩

/-- An equivalent contrapositive-style reformulation: there is no bound beyond which
all twin prime pairs stop occurring. -/
