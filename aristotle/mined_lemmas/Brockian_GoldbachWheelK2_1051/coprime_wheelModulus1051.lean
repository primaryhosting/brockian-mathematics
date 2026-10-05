import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
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

namespace Brockian

/-- The wheel modulus of this instance. -/

lemma coprime_wheelModulus1051 {k : ℕ} (hk : 0 < k) (hlt : k < wheelModulus1051) :
    Nat.Coprime k wheelModulus1051 := by
  have h : Nat.Coprime wheelModulus1051 k :=
    (Nat.Prime.coprime_iff_not_dvd prime_wheelModulus1051).2
      (Nat.not_dvd_of_pos_of_lt hk hlt)
  exact h.symm

/-- **Wheel decomposition of a residue.** Every residue class modulo the wheel modulus
`1051` is the sum of two residues that are invertible on the wheel (i.e. coprime to the
modulus). This is the combinatorial heart of the statement: it says the `K = 2` wheel
covers all of `ZMod 1051`. -/
