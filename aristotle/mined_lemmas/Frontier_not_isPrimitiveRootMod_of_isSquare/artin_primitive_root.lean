/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` if every nonzero residue class mod `p`
is a power of `a`, i.e. `a` generates the multiplicative group `(ZMod p)ˣ`. -/

theorem artin_primitive_root (a : ℤ) (h : (artinPrimes a).Infinite) :
    a ≠ -1 ∧ ¬IsSquare a := by
  constructor
  · rintro rfl
    exact h (Set.Finite.subset (Set.toFinite ({2, 3} : Set ℕ)) artinPrimes_neg_one_subset)
  · intro ha
    obtain ⟨p, hp, hp2⟩ := h.exists_gt 2
    exact not_isPrimitiveRootMod_of_isSquare ha hp.1 (by omega) hp.2

end Results

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

